(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.B08 Require Import ImageA.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.B08 Require Import Layout.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.B08 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_lits Lept_env LeptC_kit Lept_leaf LeptC_leaf LeptL_kit LeptL_padbits_loop D_iface D_defs LeptB_guard.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.






(* [comment removed for export] *)
Ltac local_acc FSH fr idx off FR64 NAME :=
  let T := fresh "T" in let T2 := fresh "T" in let T3 := fresh "T" in let B := fresh "B" in
  pose proof FSH as T; split_at T idx T2; split_at T2 1%nat T3; clear T T3;
  lazymatch type of T2 with rw_cells _ ?mm _ _ =>
    assert (NAME : acc asegs mm (fr + off) 4)
      by (destruct T2 as [[_ B] _]; apply (acc_ushadow asegs mm (fr + off) 4); [clear - FR64; Z.div_mod_to_equations; lia| lia| lia|];
          let c := eval vm_compute in (2147450880 + Z.of_nat idx) in
          replace (shad (fr + off)) with (fr / 8 + c) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
          exact B) end; clear T2.

(* [comment removed for export] *)
Lemma rmask_bytes : forall m : mem, mem_inv asegs m ->
  exists bs, bytes_at asegs m 0x23ea0 bs /\ Z.of_nat (length bs) = 132.
Proof.
  intros m MI. destruct (image_bytes asegs 0x23ea0 132) as [bs|] eqn:IB; [| vm_compute in IB; discriminate IB].
  assert (OK : ro_bytes_b asegs 0x23ea0 bs = true) by (vm_compute in IB; injection IB as <-; vm_compute; reflexivity).
  pose proof (Lept_lits.image_bytes_length _ _ _ IB) as LB.
  exists bs. split; [apply ro_bytes_at; [exact MI| lia| rewrite LB; lia| apply ro_bytes_b_sound; exact OK]| rewrite LB; reflexivity].
Qed.

Section PB.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis STDERR : lept_stderr_cps RT.
Hypothesis RERR : returnError_cps RT e_returnErrorInt.

Theorem pixSetPadBits_ok : pixSetPadBits_cps RT.
Proof using AF GP STDERR RERR.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pix v cv
    FDO MST -> -> -> PO PD ENV RES.
  unfold lpost, lenv, lres, keeps, keepsL in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct RES as (FRB & LVB & CRB & LVP).
  destruct PO as (PXC & (INP & PX0 & PX16 & _) & HOK & DAT & _).
  destruct DAT as [E|((IND & DA0 & DA16 & DAN) & DNE)]; [contradiction|].
  destruct v as [w h d spp wpl xres yres inf spec pcm data].
  cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data] in *.
  unfold pix_cells in PXC. cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data] in PXC.
  unfold rsize in *. cbn [p_wpl p_h] in *.
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, e_pixSetPadBits, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold LSTK, STDERR_STACK in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  pose proof ST as (STa & STb & _).
  lib_refresh RT GP.
  pose proof RERR as RE. unfold returnError_cps in RE. pose proof STDERR as SE. unfold lept_stderr_cps in SE.
  set (PF := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a /\ outside [(data, data + 4 * (wpl * h))] a).
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a [Ha _]. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]. }
  assert (DPR : 1 <= d <= 32) by (destruct HOK as (HDP & _); clear - HDP; cbn [In p_d] in HDP; lia).
  assert (WPR : 0 < w <= 20000) by (destruct HOK as (_ & HW & _); cbn [p_w] in HW; exact HW).
  assert (HPR : 0 < h <= 20000) by (destruct HOK as (_ & _ & HH & _); cbn [p_h] in HH; exact HH).
  assert (PR : 0 < d * w <= 640000) by (clear - DPR WPR; nia).
  chunk_facts RT AF GP pix 64. chunk_facts RT AF GP data (4 * (wpl * h)).
  pose proof (live_apart RT AF Σ m data (4 * (wpl * h)) pix 64 ART0 IND INP DNE) as DPD.
  assert (AL : usp mod 32 = 0 \/ usp mod 32 = 16) by (Z.div_mod_to_equations; lia).
  park_disj.
  destruct AL as [AL|AL].
  - (* [comment removed for export] *)
    carve_frame 128%nat ST.
    clear_acc.
    Time walk_to AF MST [(usp - 128, usp)] [0x48b74].
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                  ltac:(fun Hx => cbn [outside]; split; [destruct (PFS _ Hx); lia| exact I]).
    eapply cps_seq.
    { eapply (gp_stack_malloc_1 RT GP) with (lo := lo); rt_side idtac. }
    after_call RT AF.
    fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [auto| auto| lia]).
    fframe_open RT AF PF (rt_live RT Σ) usp 1%nat 128 ltac:(fun Ha => exact (proj1 Ha)).
    pose proof (proj2 FRM) as WFR. pose proof (proj2 FSH) as WFS. cbn [cells_size csize Nat.add] in WFR, WFS.
    change (Z.of_nat 120) with 120 in WFR. change (Z.of_nat 16) with 16 in WFS.
    fframe_chunk RT AF fr 1%nat 128 pix 64.
    fframe_chunk RT AF fr 1%nat 128 data (4 * (wpl * h)).
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. clear_acc. park_disj.
    Time walk_to AF MST [(usp - 128, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x9167c].
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
    lazymatch goal with MUx : munch _ ?mm _ |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                         repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *.
    (* [comment removed for export] *)
    lazymatch goal with FRx : rw_cells asegs _ (usp + -128) ?cs |- _ =>
      assert (EPI : forall (S : rts RT) (mE : mem)
                (r1 r5 r6 r7 r9 r10 r11 r12 r13 r14 r15 r16 r17 r19 r20 r21 r22 r23 r24 r27 r28 r29 r30 r31 : word) F' fc',
          ART RT S mE -> mem_inv asegs mE -> stk asegs mE lo (usp + -128) -> rw_cells asegs mE (usp + -128) cs ->
          wr_at asegs mE fr 120 -> wr_at asegs mE (fr / 8 + 2147450880) 16 ->
          LIBH mE -> io_ssp mE -> agree_on PF m mE -> wmono asegs m mE ->
          rt_frames RT S = (fr, 1%nat) :: rt_frames RT Σ -> rt_live RT S = rt_live RT Σ -> rt_sp0 RT S = rt_sp0 RT Σ ->
          rt_credit RT Σ - 3 <= rt_credit RT S ->
          cps asegs (ASTA RT S PMc (eq (entry_st r1 (Z_to_bv 64 (usp + -128)) gp (Z_to_bv 64 TP_A) r5 r6 r7 (Z_to_bv 64 usp) r9
                                          r10 r11 r12 r13 r14 r15 r16 r17 (Z_to_bv 64 fr) r19 r20 r21 r22 r23 r24
                                          (Z_to_bv 64 (fr / 8 + 2147450880)) (Z_to_bv 64 fr) r27 r28 r29 r30 r31 F' fc' 0x918c0 mE))) QF) end.
    { intros S mE r1 r5 r6 r7 r9 r10 r11 r12 r13 r14 r15 r16 r17 r19 r20 r21 r22 r23 r24 r27 r28 r29 r30 r31 F' fc'
        ARTE MIE STE FRE WFE WSE LHE SSPE AGE WME EFR ELV ESP0 ECR.
      clear AGF. rename AGE into AGF.
      repeat match goal with H : rw_cells asegs _ _ _ |- _ => lazymatch H with FRE => fail | _ => clear H end end.
      repeat match goal with H : ro_cells asegs _ _ _ |- _ => clear H end.
      repeat match goal with H : ART RT _ _ |- _ => lazymatch H with ARTE => fail | _ => clear H end end.
      repeat match goal with H : LIBH _ |- _ => lazymatch H with LHE => fail | _ => clear H end end.
      repeat match goal with H : io_ssp _ |- _ => lazymatch H with SSPE => fail | _ => clear H end end.
      repeat match goal with H : stk asegs _ _ _ |- _ => lazymatch H with STE => fail | _ => clear H end end.
      repeat match goal with H : mem_inv asegs _ |- _ => lazymatch H with MIE => fail | _ => clear H end end.
      repeat match goal with H : wmono asegs _ _ |- _ => lazymatch H with WME => fail | _ => clear H end end.
      repeat match goal with H : munch _ _ _ |- _ => clear H end.
      clear_acc.
      destruct (wr_at_rw_CB mE fr 120 WFE ltac:(lia)) as (jfE & FRME). destruct (wr_at_rw_CB mE (fr / 8 + 2147450880) 16 WSE ltac:(lia)) as (jsE & FSHE).
      change (Z.to_nat 120) with 120%nat in FRME. change (Z.to_nat 16) with 16%nat in FSHE.
      unfold entry_st.
      Time walk_to AF MST [(usp - 128, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x91924].
      Time frame_release_g RT AF GP MST Σ fr 1%nat 128 PF AGF PFS usp lo 0x9192c
        ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
        ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                        repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia])
        ltac:(fun Hx => exact (proj1 Hx))
        ltac:(fun fl FLN => repeat match goal with H : rw_cells asegs _ fr _ |- _ => clear H | H : rw_cells asegs _ (fr / 8 + 2147450880) _ |- _ => clear H end).
      Time walk_to AF MST [(usp - 128, usp)] (@nil Z).
      cps_stop.
      art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I]).
      lazymatch goal with MUx : munch _ ?mm _ |- _ =>
        agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]) end.
      apply cps_finish. intros c Hc. subst QF. cbv beta.
      lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S end. eexists.
      split.
      + eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-. eexists. split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
        split; [split; [split; [assumption| split; [assumption| split; [| assumption]]]| split; assumption]|].
        * lazymatch goal with WMx : wmono asegs m ?mf |- wmono asegs m ?mf => exact WMx end.
        * intros a Ha Ho. apply AGF. split; [| exact Ho].
          repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H in Ha end. exact Ha.
      + repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end.
        repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end.
        repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end.
        repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end.
        repeat split; auto; lia.
    }
    lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ (eq (MS _ _ _ _ _ ?mm _))) _ =>
      pose proof (gp_acc_rmask RT GP S mm A) as ACCR; unfold LEPT_RMASK32 in ACCR end.
    local_acc FSH fr 4%nat 32 FR64 ACCW. local_acc FSH fr 6%nat 48 FR64 ACCH. local_acc FSH fr 8%nat 64 FR64 ACCD.
    Time walk_to AF MST [(usp - 192, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16); (data, data + 4 * (wpl * h))]
                        [0x8d858; 0x8d824; 0x918c0].
    sx32_fix. brfork HD32.
    1:{ (* [comment removed for export] *)
      cwalk [0x8d858; 0x8d824; 0x918c0].
    cps_stop.
    art_now RT AF
ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac|
                         split; [intros zz Hzz; right; right; left; exists data, (4 * (wpl * h)); split; [solve [in_live_tac]| lia]| exact I]]]])
    .
    lazymatch goal with MUx : munch _ ?mm _ |- _ => agf_munch AGF MUx
ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; destruct Hx as [_ Hx2]; cbn [outside] in Hx2;
                                  unfold shad, SHB in *; repeat split; try exact I; first [tauto | lia | Z.div_mod_to_equations; lia])
    end.
    to_entry.
    eapply EPI; try eassumption.
    all: lazymatch goal with
         | |- _ <= _ => repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end; lia
         | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
         | |- rt_live _ _ = _ => repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity
         | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
         | |- _ => idtac
         end.
    }
    cwalk [0x8d858; 0x8d824; 0x918c0].
    brfork HD24.
    2:{ (* [comment removed for export] *)
      cwalk [0x8d858; 0x8d824; 0x918c0].
    at_call RT AF
ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac|
                         split; [intros zz Hzz; right; right; left; exists data, (4 * (wpl * h)); split; [solve [in_live_tac]| lia]| exact I]]]])
ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; destruct Hx as [_ Hx2]; cbn [outside] in Hx2;
                                  unfold shad, SHB in *; repeat split; try exact I; first [tauto | lia | Z.div_mod_to_equations; lia])
    .
    eapply cps_seq.
    { eapply SE with (lo := lo) (kinds := [true]); rt_side idtac.
      all: lazymatch goal with
           | |- lept_args_lit _ _ => args_lit_tac
           | |- (_ < _)%nat => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; cbn [length]; unfold FRAMES_MAX in *; lia
           | |- _ <= rt_credit _ _ => repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end; lia
           | |- ?g => idtac "LEFTOVER:" g
           end. }
    after_call RT AF.
    fold_ag ltac:(fun Hx => destruct Hx as [Hx1 _]; apply (aclient_mono _ _ usp _ _ _ _ Hx1); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]).
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. park_disj.
    walk_to AF MST [(usp - 192, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16); (data, data + 4 * (wpl * h))] [0x918c0].
    cps_stop.
    art_now RT AF
ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac|
                         split; [intros zz Hzz; right; right; left; exists data, (4 * (wpl * h)); split; [solve [in_live_tac]| lia]| exact I]]]])
    .
    lazymatch goal with MUx : munch _ ?mm _ |- _ => agf_munch AGF MUx
ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; destruct Hx as [_ Hx2]; cbn [outside] in Hx2;
                                  unfold shad, SHB in *; repeat split; try exact I; first [tauto | lia | Z.div_mod_to_equations; lia])
    end.
    to_entry.
    eapply EPI; try eassumption.
    all: lazymatch goal with
         | |- _ <= _ => repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end; lia
         | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
         | |- rt_live _ _ = _ => repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity
         | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
         | |- _ => idtac
         end.
    }
    cwalk [0x8d858; 0x8d824; 0x918c0].
    (* [comment removed for export] *)
    sx32_fix. rewrite !(unsigned_lit d) by lia. rewrite !(unsigned_lit w) by lia.
    set (P := d * w) in *.
    rewrite !(signed_lit64 P) by lia.
    replace (P / 9223372036854775808) with 0 by (symmetry; apply Z.div_small; lia).
    change (0 mod 18446744073709551616 / 576460752303423488) with 0.
    rewrite Z.add_0_r. rewrite !(Z.mod_small P 18446744073709551616) by lia.
    rewrite (land_m32 P) by lia.
    brfork HEB.
    1:{ (* [comment removed for export] *)
      cwalk [0x8d858; 0x8d824; 0x918c0].
    cps_stop.
    art_now RT AF
ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac|
                         split; [intros zz Hzz; right; right; left; exists data, (4 * (wpl * h)); split; [solve [in_live_tac]| lia]| exact I]]]])
    .
    lazymatch goal with MUx : munch _ ?mm _ |- _ => agf_munch AGF MUx
ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; destruct Hx as [_ Hx2]; cbn [outside] in Hx2;
                                  unfold shad, SHB in *; repeat split; try exact I; first [tauto | lia | Z.div_mod_to_equations; lia])
    end.
    to_entry.
    eapply EPI; try eassumption.
    all: lazymatch goal with
         | |- _ <= _ => repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end; lia
         | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
         | |- rt_live _ _ = _ => repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity
         | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
         | |- _ => idtac
         end.
    }
    cwalk [0x8d858; 0x8d824; 0x918c0; 0x917d0].
    (* [comment removed for export] *)
    lazymatch goal with MIx : mem_inv asegs ?mm |- evt _ _ (MS ?R _ _ _ _ ?mm _) =>
      destruct (rmask_bytes mm MIx) as (rbs & RB & RBL);
      destruct (bytes_at_read4w mm 0x23ea0 rbs ((32 - (P - 32 * (P / 32))) * 4) RB
                  ltac:(clear - PR0 PR1; Z.div_mod_to_equations; lia) ltac:(rewrite RBL; clear - PR0 PR1; Z.div_mod_to_equations; lia)) as (wm & RM) end.
    lstep. clear RM RB.
    cwalk [0x8d858; 0x8d824; 0x918c0; 0x917d0].
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (EWPL : wpl = (P + 31) / 32) by (destruct HOK as (_ & _ & _ & HWPL & _); cbn [p_w p_d p_wpl] in HWPL; unfold P; replace (d * w) with (w * d) by ring; exact HWPL).
    assert (HSZ : 4 * (wpl * h) <= 67108864) by (destruct HOK as (_ & _ & _ & _ & HSZ); cbn [p_wpl p_h] in HSZ; clear - HSZ; lia).
    assert (WPLR : 0 < wpl <= 2^20) by (clear - EWPL PR0 PR1; Z.div_mod_to_equations; lia).
    assert (FWR : 0 <= P / 32 < wpl) by (clear - EWPL PR0 PR1 HEB; Z.div_mod_to_equations; lia).
    lazymatch goal with WMx : wmono asegs m ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (wr_at_transport asegs m mm data (4 * (wpl * h)) (proj1 (af_acc_live RT AF Σ m data (4 * (wpl * h)) ART0 IND)) WMx) as WRD end.
    apply wr_at_rw_CB in WRD; [| clear - DAN; lia]. destruct WRD as (dbs & DBC).
    pose proof DBC as [[[DBL _] _] _]. cbn in DBL. apply u8arr_of_rw_cells in DBC.
    lazymatch type of DBC with u8arr _ ?mm _ _ =>
      destruct (u8arr_u32arr mm data dbs (wpl * h) DBC ltac:(rewrite DBL; clear - DAN; lia)) as (ws & UA & UAL) end.
    pose proof FRM as HC; split_at HC 6%nat HC2; split_at HC2 1%nat HC3; clear HC HC3.
    (* [comment removed for export] *)
    rewrite (sx32_small h) in HC2 by (clear - HPR0 HPR1; lia).
    assert (Q1 : Z.of_nat (Z.to_nat h) = h - 0) by (clear - HPR0; lia).
    assert (Q3 : (1 <= Z.to_nat h)%nat) by (clear - HPR0; lia).
    assert (Q6 : 0 < h <= 2^20) by (clear - HPR0 HPR1; lia).
    assert (Q7 : wpl * h <= 2^24) by (clear - HSZ; lia).
    assert (Q9 : data mod 8 = 0) by (clear - DA16; Z.div_mod_to_equations; lia).
    assert (Q10 : data + 4 * (wpl * h) <= 2^47) by (clear - CKR0 SP0R1; lia).
    assert (Q11 : data + 4 * (wpl * h) <= 0x7fff7000 \/ 0x10007fff8000 <= data) by (clear - CKH0; unfold parked in CKH0; lia).
    assert (Q12 : data + 4 * (wpl * h) <= 0x10000 \/ SEGTOP_A <= data) by (clear - CKS0; unfold parked, SEGTOP_A in *; lia).
    assert (Q13 : 0 < fr + 48) by (clear - FR0; lia).
    assert (Q14 : fr + 48 + 4 <= 2^47) by (clear - FRHI SP0R1; lia).
    assert (Q15 : fr + 48 + 4 <= data \/ data + 4 * (wpl * h) <= fr + 48) by (clear - FCD0; unfold parked in FCD0; lia).
    rewrite !(signed_lit64 P) by (clear - PR0 PR1; lia).
    rewrite ?Z.add_0_r.
    rewrite ?(Z.mod_small (P / 32) 18446744073709551616) by (clear - FWR WPLR; lia).
    rewrite ?(bv_swrap_small 32 (P / 32)) by (change (bv_half_modulus 32) with (2^31); clear - FWR WPLR; lia).
    rewrite ?(Z.mod_small (P / 32) 18446744073709551616) by (clear - FWR WPLR; lia).
    rewrite ?(sx32_small wpl) by (clear - WPLR; lia). rewrite ?(unsigned_lit wpl) by (clear - WPLR; lia).
    (* [comment removed for export] *)
    replace (0 <? data) with true by (symmetry; apply Z.ltb_lt; clear - DA0; lia). cbn [Z.b2z].
    change (0 + 9223372036854775808) with 9223372036854775808.
    rewrite ?(Z.mod_small (P / 32 * 4) 18446744073709551616) by (clear - FWR WPLR; lia).
    rewrite (slt0_nonneg (P / 32 * 4)) by (clear - FWR WPLR; lia). cbn [Z.b2z].
    eapply evt_cut.
    { lazymatch goal with MIx : mem_inv asegs ?mm |- evt _ _ (MS _ ?F0 _ ?fc0 None ?mm _) =>
        epose proof (padbits_rows (Z.to_nat h) 0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F0 fc0 mm data wpl h (P / 32) (fr + 48) ws
                       Q1 ltac:(lia) Q3 FWR WPLR Q6 Q7 DA0 Q9 Q10 Q11 Q12 Q13 Q14 Q15 UA UAL ACC HC2 MIx) as ZR end.
      unfold SHB in ZR.
      replace (4 * (P / 32)) with (P / 32 * 4) in ZR by (clear; lia).
        exact ZR. }
    (* [comment removed for export] *)
    intros ms' PO. unfold padbits_exit in PO.
    destruct PO as (t0' & t1' & t2' & a1' & a2' & m' & ws' & -> & MU' & WM' & MI' & UA' & UAL' & HC').
    unfold SHB.
    assert (FCS0' : data + 4 * (wpl * h) <= fr / 8 + 2147450880 \/ fr / 8 + 2147450880 + 16 <= data)
      by (clear - FCS0; unfold parked in FCS0; Z.div_mod_to_equations; lia).
    lazymatch goal with FRSx : rt_frames RT ?S = (fr, 1%nat) :: _ |- _ =>
      loop_art RT AF S m' lo MU'
ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac|
                         split; [intros zz Hzz; right; right; left; exists data, (4 * (wpl * h)); split; [solve [in_live_tac]| lia]| exact I]]]])
    end.
    clear UA UAL HC2 DBC DBL Q1 Q3 Q6 Q7 Q9 Q10 Q11 Q12 Q13 Q14 Q15 UA' UAL' HC'.
    lazymatch type of MU' with munch _ ?mm m' =>
      loop_transport mm m' MU' ltac:(fun Hx => clear - Hx CKR0 CKS0 FCD0 FCS0' DPD LOW LOR SPT SPB STa USP0 USP1; unfold parked in *; lia) end.
    clear MU' WM'.
    cwalk [0x918c0].
    cps_stop.
    art_now RT AF
ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac|
                         split; [intros zz Hzz; right; right; left; exists data, (4 * (wpl * h)); split; [solve [in_live_tac]| lia]| exact I]]]])
    .
    lazymatch goal with MUx : munch _ ?mm _ |- _ => agf_munch AGF MUx
ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; destruct Hx as [_ Hx2]; cbn [outside] in Hx2;
                                  unfold shad, SHB in *; repeat split; try exact I; first [tauto | lia | Z.div_mod_to_equations; lia])
    end.
    to_entry.
    eapply EPI; try eassumption.
    all: lazymatch goal with
         | |- _ <= _ => repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end; lia
         | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
         | |- rt_live _ _ = _ => repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity
         | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
         | |- _ => idtac
         end.
  - (* [comment removed for export] *)
    carve_frame 144%nat ST.
    clear_acc.
    Time walk_to AF MST [(usp - 144, usp)] [0x48b74].
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                  ltac:(fun Hx => cbn [outside]; split; [destruct (PFS _ Hx); lia| exact I]).
    eapply cps_seq.
    { eapply (gp_stack_malloc_1 RT GP) with (lo := lo); rt_side idtac. }
    after_call RT AF.
    fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [auto| auto| lia]).
    fframe_open RT AF PF (rt_live RT Σ) usp 1%nat 128 ltac:(fun Ha => exact (proj1 Ha)).
    pose proof (proj2 FRM) as WFR. pose proof (proj2 FSH) as WFS. cbn [cells_size csize Nat.add] in WFR, WFS.
    change (Z.of_nat 120) with 120 in WFR. change (Z.of_nat 16) with 16 in WFS.
    fframe_chunk RT AF fr 1%nat 128 pix 64.
    fframe_chunk RT AF fr 1%nat 128 data (4 * (wpl * h)).
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. clear_acc. park_disj.
    Time walk_to AF MST [(usp - 144, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x9167c].
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
    lazymatch goal with MUx : munch _ ?mm _ |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                         repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *.
    (* [comment removed for export] *)
    lazymatch goal with FRx : rw_cells asegs _ (usp + -144) ?cs |- _ =>
      assert (EPI : forall (S : rts RT) (mE : mem)
                (r1 r5 r6 r7 r9 r10 r11 r12 r13 r14 r15 r16 r17 r19 r20 r21 r22 r23 r24 r27 r28 r29 r30 r31 : word) F' fc',
          ART RT S mE -> mem_inv asegs mE -> stk asegs mE lo (usp + -144) -> rw_cells asegs mE (usp + -144) cs ->
          wr_at asegs mE fr 120 -> wr_at asegs mE (fr / 8 + 2147450880) 16 ->
          LIBH mE -> io_ssp mE -> agree_on PF m mE -> wmono asegs m mE ->
          rt_frames RT S = (fr, 1%nat) :: rt_frames RT Σ -> rt_live RT S = rt_live RT Σ -> rt_sp0 RT S = rt_sp0 RT Σ ->
          rt_credit RT Σ - 3 <= rt_credit RT S ->
          cps asegs (ASTA RT S PMc (eq (entry_st r1 (Z_to_bv 64 (usp + -144)) gp (Z_to_bv 64 TP_A) r5 r6 r7 (Z_to_bv 64 usp) r9
                                          r10 r11 r12 r13 r14 r15 r16 r17 (Z_to_bv 64 fr) r19 r20 r21 r22 r23 r24
                                          (Z_to_bv 64 (fr / 8 + 2147450880)) (Z_to_bv 64 fr) r27 r28 r29 r30 r31 F' fc' 0x918c0 mE))) QF) end.
    { intros S mE r1 r5 r6 r7 r9 r10 r11 r12 r13 r14 r15 r16 r17 r19 r20 r21 r22 r23 r24 r27 r28 r29 r30 r31 F' fc'
        ARTE MIE STE FRE WFE WSE LHE SSPE AGE WME EFR ELV ESP0 ECR.
      clear AGF. rename AGE into AGF.
      repeat match goal with H : rw_cells asegs _ _ _ |- _ => lazymatch H with FRE => fail | _ => clear H end end.
      repeat match goal with H : ro_cells asegs _ _ _ |- _ => clear H end.
      repeat match goal with H : ART RT _ _ |- _ => lazymatch H with ARTE => fail | _ => clear H end end.
      repeat match goal with H : LIBH _ |- _ => lazymatch H with LHE => fail | _ => clear H end end.
      repeat match goal with H : io_ssp _ |- _ => lazymatch H with SSPE => fail | _ => clear H end end.
      repeat match goal with H : stk asegs _ _ _ |- _ => lazymatch H with STE => fail | _ => clear H end end.
      repeat match goal with H : mem_inv asegs _ |- _ => lazymatch H with MIE => fail | _ => clear H end end.
      repeat match goal with H : wmono asegs _ _ |- _ => lazymatch H with WME => fail | _ => clear H end end.
      repeat match goal with H : munch _ _ _ |- _ => clear H end.
      clear_acc.
      destruct (wr_at_rw_CB mE fr 120 WFE ltac:(lia)) as (jfE & FRME). destruct (wr_at_rw_CB mE (fr / 8 + 2147450880) 16 WSE ltac:(lia)) as (jsE & FSHE).
      change (Z.to_nat 120) with 120%nat in FRME. change (Z.to_nat 16) with 16%nat in FSHE.
      unfold entry_st.
      Time walk_to AF MST [(usp - 144, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x91924].
      Time frame_release_g RT AF GP MST Σ fr 1%nat 128 PF AGF PFS usp lo 0x9192c
        ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
        ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                        repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia])
        ltac:(fun Hx => exact (proj1 Hx))
        ltac:(fun fl FLN => repeat match goal with H : rw_cells asegs _ fr _ |- _ => clear H | H : rw_cells asegs _ (fr / 8 + 2147450880) _ |- _ => clear H end).
      Time walk_to AF MST [(usp - 144, usp)] (@nil Z).
    lazymatch goal with ST' : stk asegs _ lo (usp + -144), FR' : rw_cells asegs _ (usp + -144) _ |- _ => release_frame FR' ST' usp end.
      cps_stop.
      art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I]).
      lazymatch goal with MUx : munch _ ?mm _ |- _ =>
        agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]) end.
      apply cps_finish. intros c Hc. subst QF. cbv beta.
      lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S end. eexists.
      split.
      + eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-. eexists. split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
        split; [split; [split; [assumption| split; [assumption| split; [| assumption]]]| split; assumption]|].
        * lazymatch goal with WMx : wmono asegs m ?mf |- wmono asegs m ?mf => exact WMx end.
        * intros a Ha Ho. apply AGF. split; [| exact Ho].
          repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H in Ha end. exact Ha.
      + repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end.
        repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end.
        repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end.
        repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end.
        repeat split; auto; lia.
    }
    lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ (eq (MS _ _ _ _ _ ?mm _))) _ =>
      pose proof (gp_acc_rmask RT GP S mm A) as ACCR; unfold LEPT_RMASK32 in ACCR end.
    local_acc FSH fr 4%nat 32 FR64 ACCW. local_acc FSH fr 6%nat 48 FR64 ACCH. local_acc FSH fr 8%nat 64 FR64 ACCD.
    Time walk_to AF MST [(usp - 208, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16); (data, data + 4 * (wpl * h))]
                        [0x8d858; 0x8d824; 0x918c0].
    sx32_fix. brfork HD32.
    1:{ (* [comment removed for export] *)
      cwalk [0x8d858; 0x8d824; 0x918c0].
    cps_stop.
    art_now RT AF
ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac|
                         split; [intros zz Hzz; right; right; left; exists data, (4 * (wpl * h)); split; [solve [in_live_tac]| lia]| exact I]]]])
    .
    lazymatch goal with MUx : munch _ ?mm _ |- _ => agf_munch AGF MUx
ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; destruct Hx as [_ Hx2]; cbn [outside] in Hx2;
                                  unfold shad, SHB in *; repeat split; try exact I; first [tauto | lia | Z.div_mod_to_equations; lia])
    end.
    to_entry.
    eapply EPI; try eassumption.
    all: lazymatch goal with
         | |- _ <= _ => repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end; lia
         | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
         | |- rt_live _ _ = _ => repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity
         | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
         | |- _ => idtac
         end.
    }
    cwalk [0x8d858; 0x8d824; 0x918c0].
    brfork HD24.
    2:{ (* [comment removed for export] *)
      cwalk [0x8d858; 0x8d824; 0x918c0].
    at_call RT AF
ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac|
                         split; [intros zz Hzz; right; right; left; exists data, (4 * (wpl * h)); split; [solve [in_live_tac]| lia]| exact I]]]])
ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; destruct Hx as [_ Hx2]; cbn [outside] in Hx2;
                                  unfold shad, SHB in *; repeat split; try exact I; first [tauto | lia | Z.div_mod_to_equations; lia])
    .
    eapply cps_seq.
    { eapply SE with (lo := lo) (kinds := [true]); rt_side idtac.
      all: lazymatch goal with
           | |- lept_args_lit _ _ => args_lit_tac
           | |- (_ < _)%nat => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; cbn [length]; unfold FRAMES_MAX in *; lia
           | |- _ <= rt_credit _ _ => repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end; lia
           | |- ?g => idtac "LEFTOVER:" g
           end. }
    after_call RT AF.
    fold_ag ltac:(fun Hx => destruct Hx as [Hx1 _]; apply (aclient_mono _ _ usp _ _ _ _ Hx1); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]).
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. park_disj.
    walk_to AF MST [(usp - 208, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16); (data, data + 4 * (wpl * h))] [0x918c0].
    cps_stop.
    art_now RT AF
ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac|
                         split; [intros zz Hzz; right; right; left; exists data, (4 * (wpl * h)); split; [solve [in_live_tac]| lia]| exact I]]]])
    .
    lazymatch goal with MUx : munch _ ?mm _ |- _ => agf_munch AGF MUx
ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; destruct Hx as [_ Hx2]; cbn [outside] in Hx2;
                                  unfold shad, SHB in *; repeat split; try exact I; first [tauto | lia | Z.div_mod_to_equations; lia])
    end.
    to_entry.
    eapply EPI; try eassumption.
    all: lazymatch goal with
         | |- _ <= _ => repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end; lia
         | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
         | |- rt_live _ _ = _ => repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity
         | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
         | |- _ => idtac
         end.
    }
    cwalk [0x8d858; 0x8d824; 0x918c0].
    (* [comment removed for export] *)
    sx32_fix. rewrite !(unsigned_lit d) by lia. rewrite !(unsigned_lit w) by lia.
    set (P := d * w) in *.
    rewrite !(signed_lit64 P) by lia.
    replace (P / 9223372036854775808) with 0 by (symmetry; apply Z.div_small; lia).
    change (0 mod 18446744073709551616 / 576460752303423488) with 0.
    rewrite Z.add_0_r. rewrite !(Z.mod_small P 18446744073709551616) by lia.
    rewrite (land_m32 P) by lia.
    brfork HEB.
    1:{ (* [comment removed for export] *)
      cwalk [0x8d858; 0x8d824; 0x918c0].
    cps_stop.
    art_now RT AF
ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac|
                         split; [intros zz Hzz; right; right; left; exists data, (4 * (wpl * h)); split; [solve [in_live_tac]| lia]| exact I]]]])
    .
    lazymatch goal with MUx : munch _ ?mm _ |- _ => agf_munch AGF MUx
ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; destruct Hx as [_ Hx2]; cbn [outside] in Hx2;
                                  unfold shad, SHB in *; repeat split; try exact I; first [tauto | lia | Z.div_mod_to_equations; lia])
    end.
    to_entry.
    eapply EPI; try eassumption.
    all: lazymatch goal with
         | |- _ <= _ => repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end; lia
         | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
         | |- rt_live _ _ = _ => repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity
         | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
         | |- _ => idtac
         end.
    }
    cwalk [0x8d858; 0x8d824; 0x918c0; 0x917d0].
    (* [comment removed for export] *)
    lazymatch goal with MIx : mem_inv asegs ?mm |- evt _ _ (MS ?R _ _ _ _ ?mm _) =>
      destruct (rmask_bytes mm MIx) as (rbs & RB & RBL);
      destruct (bytes_at_read4w mm 0x23ea0 rbs ((32 - (P - 32 * (P / 32))) * 4) RB
                  ltac:(clear - PR0 PR1; Z.div_mod_to_equations; lia) ltac:(rewrite RBL; clear - PR0 PR1; Z.div_mod_to_equations; lia)) as (wm & RM) end.
    lstep. clear RM RB.
    cwalk [0x8d858; 0x8d824; 0x918c0; 0x917d0].
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (EWPL : wpl = (P + 31) / 32) by (destruct HOK as (_ & _ & _ & HWPL & _); cbn [p_w p_d p_wpl] in HWPL; unfold P; replace (d * w) with (w * d) by ring; exact HWPL).
    assert (HSZ : 4 * (wpl * h) <= 67108864) by (destruct HOK as (_ & _ & _ & _ & HSZ); cbn [p_wpl p_h] in HSZ; clear - HSZ; lia).
    assert (WPLR : 0 < wpl <= 2^20) by (clear - EWPL PR0 PR1; Z.div_mod_to_equations; lia).
    assert (FWR : 0 <= P / 32 < wpl) by (clear - EWPL PR0 PR1 HEB; Z.div_mod_to_equations; lia).
    lazymatch goal with WMx : wmono asegs m ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (wr_at_transport asegs m mm data (4 * (wpl * h)) (proj1 (af_acc_live RT AF Σ m data (4 * (wpl * h)) ART0 IND)) WMx) as WRD end.
    apply wr_at_rw_CB in WRD; [| clear - DAN; lia]. destruct WRD as (dbs & DBC).
    pose proof DBC as [[[DBL _] _] _]. cbn in DBL. apply u8arr_of_rw_cells in DBC.
    lazymatch type of DBC with u8arr _ ?mm _ _ =>
      destruct (u8arr_u32arr mm data dbs (wpl * h) DBC ltac:(rewrite DBL; clear - DAN; lia)) as (ws & UA & UAL) end.
    pose proof FRM as HC; split_at HC 6%nat HC2; split_at HC2 1%nat HC3; clear HC HC3.
    (* [comment removed for export] *)
    rewrite (sx32_small h) in HC2 by (clear - HPR0 HPR1; lia).
    assert (Q1 : Z.of_nat (Z.to_nat h) = h - 0) by (clear - HPR0; lia).
    assert (Q3 : (1 <= Z.to_nat h)%nat) by (clear - HPR0; lia).
    assert (Q6 : 0 < h <= 2^20) by (clear - HPR0 HPR1; lia).
    assert (Q7 : wpl * h <= 2^24) by (clear - HSZ; lia).
    assert (Q9 : data mod 8 = 0) by (clear - DA16; Z.div_mod_to_equations; lia).
    assert (Q10 : data + 4 * (wpl * h) <= 2^47) by (clear - CKR0 SP0R1; lia).
    assert (Q11 : data + 4 * (wpl * h) <= 0x7fff7000 \/ 0x10007fff8000 <= data) by (clear - CKH0; unfold parked in CKH0; lia).
    assert (Q12 : data + 4 * (wpl * h) <= 0x10000 \/ SEGTOP_A <= data) by (clear - CKS0; unfold parked, SEGTOP_A in *; lia).
    assert (Q13 : 0 < fr + 48) by (clear - FR0; lia).
    assert (Q14 : fr + 48 + 4 <= 2^47) by (clear - FRHI SP0R1; lia).
    assert (Q15 : fr + 48 + 4 <= data \/ data + 4 * (wpl * h) <= fr + 48) by (clear - FCD0; unfold parked in FCD0; lia).
    rewrite !(signed_lit64 P) by (clear - PR0 PR1; lia).
    rewrite ?Z.add_0_r.
    rewrite ?(Z.mod_small (P / 32) 18446744073709551616) by (clear - FWR WPLR; lia).
    rewrite ?(bv_swrap_small 32 (P / 32)) by (change (bv_half_modulus 32) with (2^31); clear - FWR WPLR; lia).
    rewrite ?(Z.mod_small (P / 32) 18446744073709551616) by (clear - FWR WPLR; lia).
    rewrite ?(sx32_small wpl) by (clear - WPLR; lia). rewrite ?(unsigned_lit wpl) by (clear - WPLR; lia).
    (* [comment removed for export] *)
    replace (0 <? data) with true by (symmetry; apply Z.ltb_lt; clear - DA0; lia). cbn [Z.b2z].
    change (0 + 9223372036854775808) with 9223372036854775808.
    rewrite ?(Z.mod_small (P / 32 * 4) 18446744073709551616) by (clear - FWR WPLR; lia).
    rewrite (slt0_nonneg (P / 32 * 4)) by (clear - FWR WPLR; lia). cbn [Z.b2z].
    eapply evt_cut.
    { lazymatch goal with MIx : mem_inv asegs ?mm |- evt _ _ (MS _ ?F0 _ ?fc0 None ?mm _) =>
        epose proof (padbits_rows (Z.to_nat h) 0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F0 fc0 mm data wpl h (P / 32) (fr + 48) ws
                       Q1 ltac:(lia) Q3 FWR WPLR Q6 Q7 DA0 Q9 Q10 Q11 Q12 Q13 Q14 Q15 UA UAL ACC HC2 MIx) as ZR end.
      unfold SHB in ZR.
      replace (4 * (P / 32)) with (P / 32 * 4) in ZR by (clear; lia).
        exact ZR. }
    (* [comment removed for export] *)
    intros ms' PO. unfold padbits_exit in PO.
    destruct PO as (t0' & t1' & t2' & a1' & a2' & m' & ws' & -> & MU' & WM' & MI' & UA' & UAL' & HC').
    unfold SHB.
    assert (FCS0' : data + 4 * (wpl * h) <= fr / 8 + 2147450880 \/ fr / 8 + 2147450880 + 16 <= data)
      by (clear - FCS0; unfold parked in FCS0; Z.div_mod_to_equations; lia).
    lazymatch goal with FRSx : rt_frames RT ?S = (fr, 1%nat) :: _ |- _ =>
      loop_art RT AF S m' lo MU'
ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac|
                         split; [intros zz Hzz; right; right; left; exists data, (4 * (wpl * h)); split; [solve [in_live_tac]| lia]| exact I]]]])
    end.
    clear UA UAL HC2 DBC DBL Q1 Q3 Q6 Q7 Q9 Q10 Q11 Q12 Q13 Q14 Q15 UA' UAL' HC'.
    lazymatch type of MU' with munch _ ?mm m' =>
      loop_transport mm m' MU' ltac:(fun Hx => clear - Hx CKR0 CKS0 FCD0 FCS0' DPD LOW LOR SPT SPB STa USP0 USP1; unfold parked in *; lia) end.
    clear MU' WM'.
    cwalk [0x918c0].
    cps_stop.
    art_now RT AF
ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac|
                         split; [intros zz Hzz; right; right; left; exists data, (4 * (wpl * h)); split; [solve [in_live_tac]| lia]| exact I]]]])
    .
    lazymatch goal with MUx : munch _ ?mm _ |- _ => agf_munch AGF MUx
ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; destruct Hx as [_ Hx2]; cbn [outside] in Hx2;
                                  unfold shad, SHB in *; repeat split; try exact I; first [tauto | lia | Z.div_mod_to_equations; lia])
    end.
    to_entry.
    eapply EPI; try eassumption.
    all: lazymatch goal with
         | |- _ <= _ => repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end; lia
         | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
         | |- rt_live _ _ = _ => repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity
         | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
         | |- _ => idtac
         end.
Qed.
End PB.
