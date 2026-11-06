(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.B17 Require Import ImageA.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr FP.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.B17 Require Import Layout.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.B17 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit Lept_chain Lept_leaf Lept_objkit Lept_deserkit Km_setelem Km_iface Km_walkkit Km_gpkit.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.B17 Require Import LeptB_guard LeptB_guard2 LeptB_guard3.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* [comment removed for export] *)
Local Ltac frame_release_x RT AF GP MST Σ0 fr k SZ PF AGF PFS usp lo pcafter ivt pft xf :=
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
    xf fl FLN;
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

Section GETPIXEL.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Hypothesis GP : rt_gaps RT.

Theorem pixGetPixel_ok : pixGetPixel_cps RT.
Proof using AF RC GP.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pix v cv x y pv x0
    FDO MST -> -> -> -> -> POBJ D8 DNZ XB YB OPV PVC ENV RES.
  unfold lpost, lenv, lres, keeps, keepsL in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct RES as (FRB & LVB & CRB & LVP).
  unfold optrF in OPV. destruct OPV as (OWV & PV0 & PV8 & PVH & PVS).
  pose proof POBJ as (PXC & (PIN & PX0 & PX16 & _) & HOK & [DZ|((IND & D0 & D16 & _) & DNP)] & _); [contradiction|].
  (* [comment removed for export] *)
  assert (LOC : pv + 4 <= lo /\ (pv + 4 <= pix \/ pix + 64 <= pv) /\ (pv + 4 <= p_data v \/ p_data v + rsize v <= pv)).
  { destruct OWV as (f & k & Hin & Q1 & Q2 & _). pose proof (af_frames_range RT AF Σ m f k ART0 Hin) as (_ & R1 & _ & R2).
    pose proof (R2 pix 64 PIN). pose proof (R2 (p_data v) (rsize v) IND). unfold STACK_WIN in *. lia. }
  destruct LOC as (PVLO & PVPX & PVDT).
  (* [comment removed for export] *)
  pose proof (or_intror OWV : accok (rt_live RT Σ) (rt_frames RT Σ) m pv 4) as ACCV.
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, e_pixGetPixel, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold LSTK, STDERR_STACK in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  pose proof ST as (STa & STb & _).
  set (PF := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a /\ outside [(pv, pv + 4)] a).
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a [Ha _]. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [HH|HH]; [left; exact HH| right; unfold STACK_WIN in HH; lia]. }
  assert (AL : usp mod 32 = 0 \/ usp mod 32 = 16) by (Z.div_mod_to_equations; lia).
  destruct AL as [AL|AL].
  - (* [comment removed for export] *)
    carve_frame 160%nat ST.
    (* [comment removed for export] *)
    walk_to AF MST [(usp - 160, usp)] [e_stack_malloc 1%nat; e_returnErrorInt; e_lept_stderr; 0x8ee04].
    idtac "G1-WALK".
    (* [comment removed for export] *)
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
    eapply cps_seq.
    { pose proof (gp_stack_malloc_1 RT GP) as SM0; unfold stack_malloc_contract' in SM0; eapply SM0 with (lo := lo); rt_side idtac. }
    after_call RT AF.
    fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]).
    fframe_open RT AF PF (rt_live RT Σ) usp 1%nat 128 ltac:(fun Ha => exact (proj1 Ha)).
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
    idtac "G2-FRAME".
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch goal with A : ART RT ?S ?mm, FRS0 : rt_frames RT ?S = (fr, 1%nat) :: ?frs0 |- cps _ (ASTA RT ?S _ _) _ =>
      assert (PVF : (pv + 4 <= fr \/ fr + 128 <= pv) /\ (pv + 4 <= fr / 8 + 2147450880 \/ fr / 8 + 2147450880 + 16 <= pv));
      [ pose proof (accok_aclient (rt_live RT Σ) (rt_frames RT Σ) _ usp pv 4 pv ACCV ltac:(lia)) as AC0;
        pose proof (accok_aclient (rt_live RT Σ) (rt_frames RT Σ) _ usp pv 4 (pv + 3) ACCV ltac:(lia)) as AC3;
        pose proof (new_frame_apart RT AF S mm fr 1%nat frs0 (rt_live RT Σ) usp pv A FRS0
                      ltac:(intros e He; repeat match goal with E : rt_live _ _ = _ |- _ => rewrite E end; exact He)
                      ltac:(repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; lia)
                      ltac:(repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; unfold STACK_WIN; lia)
                      ltac:(repeat match goal with E : rt_frames _ _ = _ |- _ => rewrite E in AC0 end; exact AC0)) as N0;
        pose proof (new_frame_apart RT AF S mm fr 1%nat frs0 (rt_live RT Σ) usp (pv + 3) A FRS0
                      ltac:(intros e He; repeat match goal with E : rt_live _ _ = _ |- _ => rewrite E end; exact He)
                      ltac:(repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; lia)
                      ltac:(repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; unfold STACK_WIN; lia)
                      ltac:(repeat match goal with E : rt_frames _ _ = _ |- _ => rewrite E in AC3 end; exact AC3)) as N3;
        change (fs_size 1) with 128 in N0, N3; unfold shad, SHB in N0, N3; clear - N0 N3 FR64 PV8; Z.div_mod_to_equations; lia
      | ] end.
    idtac "G2B-PVF".
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (LVPV : forall q n, In (q, n) (rt_live RT Σ) -> q + n <= pv \/ pv + 4 <= q).
    { destruct OWV as (f & k & Hin & Q1 & Q2 & _). pose proof (af_frames_range RT AF Σ m f k ART0 Hin) as (_ & _ & _ & R2).
      intros q n Hq. pose proof (R2 q n Hq). lia. }
    lazymatch goal with |- cps _ (ASTA RT ?S _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
      assert (KL0 : keeps_live (rt_live RT Σ) m mb)
        by (intros bb kk Hin a Ha; apply AGF; split; [right; right; left; exists bb, kk; split; [exact Hin| exact Ha]
                                                     | cbn [outside]; pose proof (LVPV bb kk Hin); split; [lia | exact I]]);
      pose proof (pix_obj_keep _ m mb pix v cv KL0 POBJ) as POBJ1 end.
    pose proof POBJ1 as (PXC1 & _). unfold pix_cells in PXC1.
    (* [comment removed for export] *)
    assert (PVPX1 : pv + 4 <= pix \/ pix + 64 <= pv) by (unfold parked in *; clear - PVPX; lia).
    chunk_facts RT AF GP pix 64.
    idtac "G2C-POBJ1".
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    chunk_facts RT AF GP (p_data v) (4 * (p_wpl v * p_h v)).
    idtac "G2D-RASTER".
    (* [comment removed for export] *)
    fframe_chunk RT AF fr 1%nat 128 pix 64. norm_fshadow.
    walk_to AF MST [(usp - 160, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16); (pv, pv + 4)]
                 [e_stack_malloc 1%nat; e_returnErrorInt; e_lept_stderr; 0x8ee04; e_pixGetDimensions; e_pixGetWpl; e_pixGetData].
    idtac "G3-WALK".
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    pose proof FSH as TW. split_at TW 4%nat TW2. split_at TW2 1%nat TW3. clear TW TW3.
    lazymatch type of TW2 with rw_cells _ ?mm _ _ =>
      assert (ACCW : acc asegs mm (fr + 32) 4)
        by (destruct TW2 as [[_ B] _]; apply (acc_ushadow asegs mm (fr + 32) 4); [clear - FR64; Z.div_mod_to_equations; lia| lia| lia|];
            replace (shad (fr + 32)) with (fr / 8 + 2147450884) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia); exact B) end.
    clear TW2.
    pose proof FSH as TH. split_at TH 6%nat TH2. split_at TH2 1%nat TH3. clear TH TH3.
    lazymatch type of TH2 with rw_cells _ ?mm _ _ =>
      assert (ACCH : acc asegs mm (fr + 48) 4)
        by (destruct TH2 as [[_ B] _]; apply (acc_ushadow asegs mm (fr + 48) 4); [clear - FR64; Z.div_mod_to_equations; lia| lia| lia|];
            replace (shad (fr + 48)) with (fr / 8 + 2147450886) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia); exact B) end.
    clear TH2.
    pose proof FSH as TD. split_at TD 8%nat TD2. split_at TD2 1%nat TD3. clear TD TD3.
    lazymatch type of TD2 with rw_cells _ ?mm _ _ =>
      assert (ACCD : acc asegs mm (fr + 64) 4)
        by (destruct TD2 as [[_ B] _]; apply (acc_ushadow asegs mm (fr + 64) 4); [clear - FR64; Z.div_mod_to_equations; lia| lia| lia|];
            replace (shad (fr + 64)) with (fr / 8 + 2147450888) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia); exact B) end.
    clear TD2.
    idtac "G5-ACC".
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac|
                          split; [intros zz Hzz; apply (aclient_mono (rt_live RT Σ) (rt_frames RT Σ) usp _ _ _ zz
                                                          (accok_aclient _ _ m usp pv 4 zz (or_intror OWV) ltac:(lia)));
                                  [solve [live_sub_tac]| solve [frames_sub_tac]| lia]
                                 | exact I]]]]).
    idtac "G6-ART".
    (* [comment removed for export] *)
    lazymatch goal with MUx : munch _ ?mm _ |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => pose proof (PFS _ Hx) as HxS; destruct (NFA _ Hx) as [N1 N2]; destruct Hx as [_ HO]; cbn [outside] in HO |- *;
                                        unfold shad, SHB in *; repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
    idtac "G7-AGF".
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
    walk_to AF MST [(usp - 256, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16); (pv, pv + 4)]
                 [e_stack_malloc 1%nat; e_returnErrorInt; e_lept_stderr; 0x8ee04].
    idtac "G7-WALK".
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    pose proof HOK as (HDIN & HWR & HHR & HWPL & HRS).
    (* [comment removed for export] *)
    lazymatch goal with H : rw_cells _ _ fr (C8 _ :: _) |- _ =>
      rewrite ?(sx32_small (p_w v)) in H by lia; rewrite ?(sx32_small (p_h v)) in H by lia; rewrite ?(sx32_small (p_d v)) in H by lia end.
    assert (WPLR : 0 < p_wpl v <= 20000) by (rewrite HWPL, D8; Z.div_mod_to_equations; lia).
    try brF.
    awalk [e_stack_malloc 1%nat; e_returnErrorInt; e_lept_stderr; 0x8ee04].
    idtac "G8-WALK".
    (* [comment removed for export] *)
    rewrite ?(sx32_small (p_w v)) by lia. try brF.
    awalk [e_stack_malloc 1%nat; e_returnErrorInt; e_lept_stderr; 0x8ee04].
    idtac "G9-WALK".
    (* [comment removed for export] *)
    rewrite ?(sx32_small (p_h v)) by lia. try brF.
    awalk [e_stack_malloc 1%nat; e_returnErrorInt; e_lept_stderr; 0x8ee04].
    idtac "G10-WALK".
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    rewrite ?(unsigned_lit (p_wpl v)) by lia.
    assert (WY : 0 <= p_wpl v * y /\ p_wpl v * y + p_wpl v <= p_wpl v * p_h v) by (split; nia).
    rewrite ?(bv_swrap_small 32 (y * p_wpl v)) by (change (bv_half_modulus 32) with (2^31); lia).
    idtac "G10B-SWRAP".
    brF.
    awalk [e_stack_malloc 1%nat; e_returnErrorInt; e_lept_stderr; 0x8ee04].
    idtac "G10B-WALK".
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    rewrite !D8.
    awalk [e_stack_malloc 1%nat; e_returnErrorInt; e_lept_stderr; 0x8ee04].
    idtac "G11-WALK".
    (* [comment removed for export] *)
    lstep.
    idtac "G12-JR".
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    rewrite ?Z.add_0_r.
    assert (WY4 : 0 <= y * p_wpl v < 2^24) by nia.
    rewrite ?(Z.mod_small (y * p_wpl v) 18446744073709551616) by lia.
    rewrite ?(Z.mul_comm y (p_wpl v)).
    lstep.
    idtac "G13-ADD".
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (W4 : p_w v <= 4 * p_wpl v) by (rewrite HWPL, D8; Z.div_mod_to_equations; lia).
    set (X := p_data v + p_wpl v * y * 4 + x) in *.
    assert (XLO : p_data v <= X) by (unfold X; lia).
    assert (XHI : X + 1 <= p_data v + 4 * (p_wpl v * p_h v)) by (unfold X; lia).
    assert (XW : X - X mod 4 + 4 <= p_data v + 4 * (p_wpl v * p_h v))
      by (unfold X; clear - D16 XB0 XB1 W4 WY; Z.div_mod_to_equations; lia).
    assert (X0 : 0 <= X) by lia.
    idtac "G14-X".
    (* [comment removed for export] *)
    awalk [e_stack_malloc 1%nat; e_returnErrorInt; e_lept_stderr; 0x8f110].
    idtac "G14B-WALK".
    (* [comment removed for export] *)
    lstep. lstep.
    shload. lstep.
    lstep.
    (* [comment removed for export] *)
    change (p_data v + p_wpl v * y * 4 + x) with X.
    idtac "G15-STEPS".
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    rewrite (lxor3_decomp X X0).
    assert (OKW : sh_ok shb11 (X + (4 - X mod 4) - 1))
      by (apply (shk_ok m2 (p_data v) (4 * (p_wpl v * p_h v)) X (4 - X mod 4) shb11 ACC SHK);
          clear - XLO XW X0; Z.div_mod_to_equations; lia).
    assert (BB : 0 <= bv_unsigned shb11 < 8) by (pose proof (bv_unsigned_in_range 8 shb11); destruct OKW as [?|[? ?]]; lia).
    rewrite !(sxb_small shb11) by lia.
    assert (XN : 0 <= 4 * (X / 4) + (3 - X mod 4)) by (clear - X0; Z.div_mod_to_equations; lia).
    idtac "G16-OKW".
    (* [comment removed for export] *)
    lstep.   (* [comment removed for export] *)
    lazymatch goal with
    | |- evt ?segs ?Q (MS ?R ?F _ ?fc ?rv ?m ?ro) =>
      eapply (evt_cut segs (fun ms' => exists u' : word,
                 ms' = MS (@bvmap_set 5 word (Z_to_bv 5 12) u' R) F (Z_to_bv 64 586020) fc rv m ro))
    end.
    { destruct OKW as [OK|[OK1 OK2]].
      - (* [comment removed for export] *)
        brF. apply evt_done.
        lazymatch goal with |- exists u', _ = MS (@bvmap_set 5 word ?r u' ?R') _ _ _ _ _ _ =>
          let p := eval vm_compute in (bv_key r) in
          let v := eval cbv beta iota delta [tget mkR] in (tget p R') in
          lazymatch v with Some ?x => exists x end end;
        norm_regset; reflexivity.
      - (* [comment removed for export] *)
        brT. lstep. lstep.
        assert (XM : (4 * (X / 4) + (3 - X mod 4)) mod 8 < bv_unsigned shb11) by (clear - OK2 X0; Z.div_mod_to_equations; lia).
        brT. apply evt_done. eexists. norm_regset. reflexivity. }
    intros ms (u' & E); subst ms; norm_regset. clear OKW.
    idtac "G17-SHMERGE".
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    pose proof (wr_at_transport asegs m m2 (p_data v) (4 * (p_wpl v * p_h v)) (proj1 (af_acc_live RT AF Σ m _ _ ART0 IND)) WM) as WRD.
    apply wr_at_rw_CB in WRD; [| lia]. destruct WRD as (dbs & DBC).
    pose proof DBC as [[[DBL _] _] _]. cbn in DBL. apply u8arr_of_rw_cells in DBC.
    assert (XAR : p_data v <= 4 * (X / 4) + (3 - X mod 4) /\ 4 * (X / 4) + (3 - X mod 4) + 1 <= p_data v + 4 * (p_wpl v * p_h v))
      by (clear - XLO XW X0 D16; Z.div_mod_to_equations; lia).
    destruct (nth_error dbs (Z.to_nat (4 * (X / 4) + (3 - X mod 4) - p_data v))) as [bx|] eqn:NB;
      [| apply nth_error_None in NB; rewrite DBL in NB; lia].
    pose proof (u8arr_read asegs m2 (p_data v) dbs (4 * (X / 4) + (3 - X mod 4) - p_data v) bx (Z_to_bv 64 (4 * (X / 4) + (3 - X mod 4)))
                  DBC NB ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RDB.
    lstep. clear RDB.
    idtac "G18-LOAD".
    (* [comment removed for export] *)
    awalk [e_stack_malloc 1%nat; e_returnErrorInt; e_lept_stderr; 0x8f018].
    idtac "G19-WALK".
    (* [comment removed for export] *)
    frame_release_x RT AF GP MST Σ fr 1%nat 128 PF AGF PFS usp lo 585760
      ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac|
              split; [intros zz Hzz; apply (aclient_mono (rt_live RT Σ) (rt_frames RT Σ) usp _ _ _ zz
                                            (accok_aclient _ _ m usp pv 4 zz (or_intror OWV) ltac:(lia)));
                      [solve [live_sub_tac]| solve [frames_sub_tac]| lia]
                     | exact I]]]])
      ltac:(fun Hx => pose proof (PFS _ Hx) as HxS; destruct (NFA _ Hx) as [N1 N2]; destruct Hx as [_ HO]; cbn [outside] in HO |- *;
                      unfold shad, SHB in *; repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia])
      ltac:(fun fl FLN => assert (FLPV : fl < pv \/ pv + 4 <= fl)
              by (apply (flag_apart _ _ fl pv (pv + 4) FLN); intros z Hz;
                  apply (aclient_mono (rt_live RT Σ) (rt_frames RT Σ) USTACK_TOP _ _ _ z (accok_aclient _ _ m USTACK_TOP pv 4 z (or_intror OWV) Hz));
                  [solve [live_sub_tac] | solve [frames_sub_tac] | lia])).
    idtac "G20-RELEASE".
    (* [comment removed for export] *)
    refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
    walk_to AF MST [(usp - 160, usp)] (@nil Z).
    try (lazymatch goal with ST' : stk asegs _ lo (usp + -160) |- _ => release_frame FR ST' usp end).
    cps_stop.
    lazymatch goal with |- cps _ (ASTA RT ?S _ (eq (MS _ _ _ _ _ ?mf _))) _ =>
      lazymatch goal with
      | _ : ART RT S mf |- _ => idtac
      | A : ART RT S ?mm, MUx : munch ?W ?mm mf, WMx : wmono asegs ?mm mf |- _ =>
          assert (ARTf : ART RT S mf)
            by (apply (art_client_writes RT AF S mm mf (usp + -160) W A MUx WMx);
                [ repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul
                | cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I] ]);
          agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I])
      end end.
    idtac "G21-END".
    (* [comment removed for export] *)
    apply cps_finish; intros c Hc; subst QF; cbv beta.
    lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S end.
    exists (bv_unsigned bx). split; [| alg_tac].
    eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-; eexists.
    split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
    split; [split; [split; [assumption| split; [assumption| split; [| assumption]]]| split; assumption]|].
    { lazymatch goal with WMx : wmono asegs m ?mf |- wmono asegs m ?mf => exact WMx end. }
    idtac "G22-A".
    split; [| split; [exact PVC | pose proof (bv_unsigned_in_range 8 bx) as BXR; unfold bv_modulus in BXR; cbn in BXR; lia]].
    idtac "G22-B".
    intros a Ha Hb. apply AGF. split; [| exact Hb].
    lazymatch type of Ha with aclient ?lv _ _ _ => replace lv with (rt_live RT Σ) in Ha by (repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity) end.
    exact Ha.
  - (* [comment removed for export] *)
    carve_frame 176%nat ST.
    (* [comment removed for export] *)
    walk_to AF MST [(usp - 176, usp)] [e_stack_malloc 1%nat; e_returnErrorInt; e_lept_stderr; 0x8ee04].
    idtac "G1-WALK".
    (* [comment removed for export] *)
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
    eapply cps_seq.
    { pose proof (gp_stack_malloc_1 RT GP) as SM0; unfold stack_malloc_contract' in SM0; eapply SM0 with (lo := lo); rt_side idtac. }
    after_call RT AF.
    fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]).
    fframe_open RT AF PF (rt_live RT Σ) usp 1%nat 128 ltac:(fun Ha => exact (proj1 Ha)).
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
    idtac "G2-FRAME".
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch goal with A : ART RT ?S ?mm, FRS0 : rt_frames RT ?S = (fr, 1%nat) :: ?frs0 |- cps _ (ASTA RT ?S _ _) _ =>
      assert (PVF : (pv + 4 <= fr \/ fr + 128 <= pv) /\ (pv + 4 <= fr / 8 + 2147450880 \/ fr / 8 + 2147450880 + 16 <= pv));
      [ pose proof (accok_aclient (rt_live RT Σ) (rt_frames RT Σ) _ usp pv 4 pv ACCV ltac:(lia)) as AC0;
        pose proof (accok_aclient (rt_live RT Σ) (rt_frames RT Σ) _ usp pv 4 (pv + 3) ACCV ltac:(lia)) as AC3;
        pose proof (new_frame_apart RT AF S mm fr 1%nat frs0 (rt_live RT Σ) usp pv A FRS0
                      ltac:(intros e He; repeat match goal with E : rt_live _ _ = _ |- _ => rewrite E end; exact He)
                      ltac:(repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; lia)
                      ltac:(repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; unfold STACK_WIN; lia)
                      ltac:(repeat match goal with E : rt_frames _ _ = _ |- _ => rewrite E in AC0 end; exact AC0)) as N0;
        pose proof (new_frame_apart RT AF S mm fr 1%nat frs0 (rt_live RT Σ) usp (pv + 3) A FRS0
                      ltac:(intros e He; repeat match goal with E : rt_live _ _ = _ |- _ => rewrite E end; exact He)
                      ltac:(repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; lia)
                      ltac:(repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; unfold STACK_WIN; lia)
                      ltac:(repeat match goal with E : rt_frames _ _ = _ |- _ => rewrite E in AC3 end; exact AC3)) as N3;
        change (fs_size 1) with 128 in N0, N3; unfold shad, SHB in N0, N3; clear - N0 N3 FR64 PV8; Z.div_mod_to_equations; lia
      | ] end.
    idtac "G2B-PVF".
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (LVPV : forall q n, In (q, n) (rt_live RT Σ) -> q + n <= pv \/ pv + 4 <= q).
    { destruct OWV as (f & k & Hin & Q1 & Q2 & _). pose proof (af_frames_range RT AF Σ m f k ART0 Hin) as (_ & _ & _ & R2).
      intros q n Hq. pose proof (R2 q n Hq). lia. }
    lazymatch goal with |- cps _ (ASTA RT ?S _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
      assert (KL0 : keeps_live (rt_live RT Σ) m mb)
        by (intros bb kk Hin a Ha; apply AGF; split; [right; right; left; exists bb, kk; split; [exact Hin| exact Ha]
                                                     | cbn [outside]; pose proof (LVPV bb kk Hin); split; [lia | exact I]]);
      pose proof (pix_obj_keep _ m mb pix v cv KL0 POBJ) as POBJ1 end.
    pose proof POBJ1 as (PXC1 & _). unfold pix_cells in PXC1.
    (* [comment removed for export] *)
    assert (PVPX1 : pv + 4 <= pix \/ pix + 64 <= pv) by (unfold parked in *; clear - PVPX; lia).
    chunk_facts RT AF GP pix 64.
    idtac "G2C-POBJ1".
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    chunk_facts RT AF GP (p_data v) (4 * (p_wpl v * p_h v)).
    idtac "G2D-RASTER".
    (* [comment removed for export] *)
    fframe_chunk RT AF fr 1%nat 128 pix 64. norm_fshadow.
    walk_to AF MST [(usp - 176, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16); (pv, pv + 4)]
                 [e_stack_malloc 1%nat; e_returnErrorInt; e_lept_stderr; 0x8ee04; e_pixGetDimensions; e_pixGetWpl; e_pixGetData].
    idtac "G3-WALK".
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    pose proof FSH as TW. split_at TW 4%nat TW2. split_at TW2 1%nat TW3. clear TW TW3.
    lazymatch type of TW2 with rw_cells _ ?mm _ _ =>
      assert (ACCW : acc asegs mm (fr + 32) 4)
        by (destruct TW2 as [[_ B] _]; apply (acc_ushadow asegs mm (fr + 32) 4); [clear - FR64; Z.div_mod_to_equations; lia| lia| lia|];
            replace (shad (fr + 32)) with (fr / 8 + 2147450884) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia); exact B) end.
    clear TW2.
    pose proof FSH as TH. split_at TH 6%nat TH2. split_at TH2 1%nat TH3. clear TH TH3.
    lazymatch type of TH2 with rw_cells _ ?mm _ _ =>
      assert (ACCH : acc asegs mm (fr + 48) 4)
        by (destruct TH2 as [[_ B] _]; apply (acc_ushadow asegs mm (fr + 48) 4); [clear - FR64; Z.div_mod_to_equations; lia| lia| lia|];
            replace (shad (fr + 48)) with (fr / 8 + 2147450886) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia); exact B) end.
    clear TH2.
    pose proof FSH as TD. split_at TD 8%nat TD2. split_at TD2 1%nat TD3. clear TD TD3.
    lazymatch type of TD2 with rw_cells _ ?mm _ _ =>
      assert (ACCD : acc asegs mm (fr + 64) 4)
        by (destruct TD2 as [[_ B] _]; apply (acc_ushadow asegs mm (fr + 64) 4); [clear - FR64; Z.div_mod_to_equations; lia| lia| lia|];
            replace (shad (fr + 64)) with (fr / 8 + 2147450888) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia); exact B) end.
    clear TD2.
    idtac "G5-ACC".
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac|
                          split; [intros zz Hzz; apply (aclient_mono (rt_live RT Σ) (rt_frames RT Σ) usp _ _ _ zz
                                                          (accok_aclient _ _ m usp pv 4 zz (or_intror OWV) ltac:(lia)));
                                  [solve [live_sub_tac]| solve [frames_sub_tac]| lia]
                                 | exact I]]]]).
    idtac "G6-ART".
    (* [comment removed for export] *)
    lazymatch goal with MUx : munch _ ?mm _ |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => pose proof (PFS _ Hx) as HxS; destruct (NFA _ Hx) as [N1 N2]; destruct Hx as [_ HO]; cbn [outside] in HO |- *;
                                        unfold shad, SHB in *; repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
    idtac "G7-AGF".
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
    walk_to AF MST [(usp - 256, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16); (pv, pv + 4)]
                 [e_stack_malloc 1%nat; e_returnErrorInt; e_lept_stderr; 0x8ee04].
    idtac "G7-WALK".
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    pose proof HOK as (HDIN & HWR & HHR & HWPL & HRS).
    (* [comment removed for export] *)
    lazymatch goal with H : rw_cells _ _ fr (C8 _ :: _) |- _ =>
      rewrite ?(sx32_small (p_w v)) in H by lia; rewrite ?(sx32_small (p_h v)) in H by lia; rewrite ?(sx32_small (p_d v)) in H by lia end.
    assert (WPLR : 0 < p_wpl v <= 20000) by (rewrite HWPL, D8; Z.div_mod_to_equations; lia).
    try brF.
    awalk [e_stack_malloc 1%nat; e_returnErrorInt; e_lept_stderr; 0x8ee04].
    idtac "G8-WALK".
    (* [comment removed for export] *)
    rewrite ?(sx32_small (p_w v)) by lia. try brF.
    awalk [e_stack_malloc 1%nat; e_returnErrorInt; e_lept_stderr; 0x8ee04].
    idtac "G9-WALK".
    (* [comment removed for export] *)
    rewrite ?(sx32_small (p_h v)) by lia. try brF.
    awalk [e_stack_malloc 1%nat; e_returnErrorInt; e_lept_stderr; 0x8ee04].
    idtac "G10-WALK".
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    rewrite ?(unsigned_lit (p_wpl v)) by lia.
    assert (WY : 0 <= p_wpl v * y /\ p_wpl v * y + p_wpl v <= p_wpl v * p_h v) by (split; nia).
    rewrite ?(bv_swrap_small 32 (y * p_wpl v)) by (change (bv_half_modulus 32) with (2^31); lia).
    idtac "G10B-SWRAP".
    brF.
    awalk [e_stack_malloc 1%nat; e_returnErrorInt; e_lept_stderr; 0x8ee04].
    idtac "G10B-WALK".
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    rewrite !D8.
    awalk [e_stack_malloc 1%nat; e_returnErrorInt; e_lept_stderr; 0x8ee04].
    idtac "G11-WALK".
    (* [comment removed for export] *)
    lstep.
    idtac "G12-JR".
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    rewrite ?Z.add_0_r.
    assert (WY4 : 0 <= y * p_wpl v < 2^24) by nia.
    rewrite ?(Z.mod_small (y * p_wpl v) 18446744073709551616) by lia.
    rewrite ?(Z.mul_comm y (p_wpl v)).
    lstep.
    idtac "G13-ADD".
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (W4 : p_w v <= 4 * p_wpl v) by (rewrite HWPL, D8; Z.div_mod_to_equations; lia).
    set (X := p_data v + p_wpl v * y * 4 + x) in *.
    assert (XLO : p_data v <= X) by (unfold X; lia).
    assert (XHI : X + 1 <= p_data v + 4 * (p_wpl v * p_h v)) by (unfold X; lia).
    assert (XW : X - X mod 4 + 4 <= p_data v + 4 * (p_wpl v * p_h v))
      by (unfold X; clear - D16 XB0 XB1 W4 WY; Z.div_mod_to_equations; lia).
    assert (X0 : 0 <= X) by lia.
    idtac "G14-X".
    (* [comment removed for export] *)
    awalk [e_stack_malloc 1%nat; e_returnErrorInt; e_lept_stderr; 0x8f110].
    idtac "G14B-WALK".
    (* [comment removed for export] *)
    lstep. lstep.
    shload. lstep.
    lstep.
    (* [comment removed for export] *)
    change (p_data v + p_wpl v * y * 4 + x) with X.
    idtac "G15-STEPS".
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    rewrite (lxor3_decomp X X0).
    assert (OKW : sh_ok shb11 (X + (4 - X mod 4) - 1))
      by (apply (shk_ok m2 (p_data v) (4 * (p_wpl v * p_h v)) X (4 - X mod 4) shb11 ACC SHK);
          clear - XLO XW X0; Z.div_mod_to_equations; lia).
    assert (BB : 0 <= bv_unsigned shb11 < 8) by (pose proof (bv_unsigned_in_range 8 shb11); destruct OKW as [?|[? ?]]; lia).
    rewrite !(sxb_small shb11) by lia.
    assert (XN : 0 <= 4 * (X / 4) + (3 - X mod 4)) by (clear - X0; Z.div_mod_to_equations; lia).
    idtac "G16-OKW".
    (* [comment removed for export] *)
    lstep.   (* [comment removed for export] *)
    lazymatch goal with
    | |- evt ?segs ?Q (MS ?R ?F _ ?fc ?rv ?m ?ro) =>
      eapply (evt_cut segs (fun ms' => exists u' : word,
                 ms' = MS (@bvmap_set 5 word (Z_to_bv 5 12) u' R) F (Z_to_bv 64 586020) fc rv m ro))
    end.
    { destruct OKW as [OK|[OK1 OK2]].
      - (* [comment removed for export] *)
        brF. apply evt_done.
        lazymatch goal with |- exists u', _ = MS (@bvmap_set 5 word ?r u' ?R') _ _ _ _ _ _ =>
          let p := eval vm_compute in (bv_key r) in
          let v := eval cbv beta iota delta [tget mkR] in (tget p R') in
          lazymatch v with Some ?x => exists x end end;
        norm_regset; reflexivity.
      - (* [comment removed for export] *)
        brT. lstep. lstep.
        assert (XM : (4 * (X / 4) + (3 - X mod 4)) mod 8 < bv_unsigned shb11) by (clear - OK2 X0; Z.div_mod_to_equations; lia).
        brT. apply evt_done. eexists. norm_regset. reflexivity. }
    intros ms (u' & E); subst ms; norm_regset. clear OKW.
    idtac "G17-SHMERGE".
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    pose proof (wr_at_transport asegs m m2 (p_data v) (4 * (p_wpl v * p_h v)) (proj1 (af_acc_live RT AF Σ m _ _ ART0 IND)) WM) as WRD.
    apply wr_at_rw_CB in WRD; [| lia]. destruct WRD as (dbs & DBC).
    pose proof DBC as [[[DBL _] _] _]. cbn in DBL. apply u8arr_of_rw_cells in DBC.
    assert (XAR : p_data v <= 4 * (X / 4) + (3 - X mod 4) /\ 4 * (X / 4) + (3 - X mod 4) + 1 <= p_data v + 4 * (p_wpl v * p_h v))
      by (clear - XLO XW X0 D16; Z.div_mod_to_equations; lia).
    destruct (nth_error dbs (Z.to_nat (4 * (X / 4) + (3 - X mod 4) - p_data v))) as [bx|] eqn:NB;
      [| apply nth_error_None in NB; rewrite DBL in NB; lia].
    pose proof (u8arr_read asegs m2 (p_data v) dbs (4 * (X / 4) + (3 - X mod 4) - p_data v) bx (Z_to_bv 64 (4 * (X / 4) + (3 - X mod 4)))
                  DBC NB ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RDB.
    lstep. clear RDB.
    idtac "G18-LOAD".
    (* [comment removed for export] *)
    awalk [e_stack_malloc 1%nat; e_returnErrorInt; e_lept_stderr; 0x8f018].
    idtac "G19-WALK".
    (* [comment removed for export] *)
    frame_release_x RT AF GP MST Σ fr 1%nat 128 PF AGF PFS usp lo 585760
      ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac|
              split; [intros zz Hzz; apply (aclient_mono (rt_live RT Σ) (rt_frames RT Σ) usp _ _ _ zz
                                            (accok_aclient _ _ m usp pv 4 zz (or_intror OWV) ltac:(lia)));
                      [solve [live_sub_tac]| solve [frames_sub_tac]| lia]
                     | exact I]]]])
      ltac:(fun Hx => pose proof (PFS _ Hx) as HxS; destruct (NFA _ Hx) as [N1 N2]; destruct Hx as [_ HO]; cbn [outside] in HO |- *;
                      unfold shad, SHB in *; repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia])
      ltac:(fun fl FLN => assert (FLPV : fl < pv \/ pv + 4 <= fl)
              by (apply (flag_apart _ _ fl pv (pv + 4) FLN); intros z Hz;
                  apply (aclient_mono (rt_live RT Σ) (rt_frames RT Σ) USTACK_TOP _ _ _ z (accok_aclient _ _ m USTACK_TOP pv 4 z (or_intror OWV) Hz));
                  [solve [live_sub_tac] | solve [frames_sub_tac] | lia])).
    idtac "G20-RELEASE".
    (* [comment removed for export] *)
    refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
    walk_to AF MST [(usp - 176, usp)] (@nil Z).
    try (lazymatch goal with ST' : stk asegs _ lo (usp + -176) |- _ => release_frame FR ST' usp end).
    cps_stop.
    lazymatch goal with |- cps _ (ASTA RT ?S _ (eq (MS _ _ _ _ _ ?mf _))) _ =>
      lazymatch goal with
      | _ : ART RT S mf |- _ => idtac
      | A : ART RT S ?mm, MUx : munch ?W ?mm mf, WMx : wmono asegs ?mm mf |- _ =>
          assert (ARTf : ART RT S mf)
            by (apply (art_client_writes RT AF S mm mf (usp + -176) W A MUx WMx);
                [ repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul
                | cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I] ]);
          agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I])
      end end.
    idtac "G21-END".
    (* [comment removed for export] *)
    apply cps_finish; intros c Hc; subst QF; cbv beta.
    lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S end.
    exists (bv_unsigned bx). split; [| alg_tac].
    eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-; eexists.
    split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
    split; [split; [split; [assumption| split; [assumption| split; [| assumption]]]| split; assumption]|].
    { lazymatch goal with WMx : wmono asegs m ?mf |- wmono asegs m ?mf => exact WMx end. }
    idtac "G22-A".
    split; [| split; [exact PVC | pose proof (bv_unsigned_in_range 8 bx) as BXR; unfold bv_modulus in BXR; cbn in BXR; lia]].
    idtac "G22-B".
    intros a Ha Hb. apply AGF. split; [| exact Hb].
    lazymatch type of Ha with aclient ?lv _ _ _ => replace lv with (rt_live RT Σ) in Ha by (repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity) end.
    exact Ha.
Qed.
End GETPIXEL.
