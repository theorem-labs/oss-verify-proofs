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
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.A17 Require Import ImageA.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr FP.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.A17 Require Import Layout.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.A17 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit Lept_chain Lept_leaf Lept_objkit Lept_deserkit Km_setelem Km_iface Km_walkkit Km_kit Km_setelem_obj Km_frompix_defs Km_frompix_exit Km_frompix_loop.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section FROMPIX.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis RERR : returnError_cps RT e_returnErrorPtr.
Hypothesis KCR : kernelCreate_cps RT.
Hypothesis GPX : pixGetPixel_cps RT.
Hypothesis KSE : kernelSetElement_cps RT.

Theorem kernelCreateFromPix_ok : kernelCreateFromPix_cps RT.
Proof using AF RC GP RERR KCR GPX KSE.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pix v cv
    FDO MST -> -> -> -> POBJ DNZ ENV RES SECB.
  unfold lpost, lenv, lres, keeps, keepsL in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct RES as (FRB & LVB & CRB & LVP).
  pose proof POBJ as (PXC & (PIN & PX0 & PX16 & _) & HOK & [DZ|((IND & D0 & D16 & _) & DNP)] & _); [contradiction|].
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, e_kernelCreateFromPix, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold LSTK, STDERR_STACK in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  pose proof ST as (STa & STb & _).
  set (PF := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a).
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a Ha. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [HH|HH]; [left; exact HH| right; unfold STACK_WIN in HH; lia]. }
  assert (AL : usp mod 32 = 0 \/ usp mod 32 = 16) by (Z.div_mod_to_equations; lia).
  destruct AL as [AL|AL].
  - (* [comment removed for export] *)

    carve_frame 128%nat ST.
    (* [comment removed for export] *)
    walk_to AF MST [(usp - 128, usp)] [e_stack_malloc 1%nat; e_returnErrorPtr; e_lept_stderr; e_kernelCreate; e_pixGetPixel; e_kernelSetElement; 0x919f8; 0x918a8].
    idtac "F1-WALK".
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
    eapply cps_seq.
    { pose proof (gp_stack_malloc_1 RT GP) as SM0; unfold stack_malloc_contract' in SM0; eapply SM0 with (lo := lo); rt_side idtac. }
    after_call RT AF.
    fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]).
    fframe_open RT AF PF (rt_live RT Σ) usp 1%nat 128 ltac:(fun Ha => exact Ha).
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
    idtac "F1-FRAME".
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch goal with |- cps _ (ASTA RT ?S _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
      assert (KL0 : keeps_live (rt_live RT Σ) m mb)
        by (intros bb kk Hin a Ha; apply AGF; right; right; left; exists bb, kk; split; [exact Hin| exact Ha]);
      pose proof (pix_obj_keep _ m mb pix v cv KL0 POBJ) as POBJ1 end.
    pose proof POBJ1 as (PXC1 & _). unfold pix_cells in PXC1.
    chunk_facts RT AF GP pix 64.
    chunk_facts RT AF GP (p_data v) (4 * (p_wpl v * p_h v)).
    fframe_chunk RT AF fr 1%nat 128 pix 64. norm_fshadow.
    walk_to AF MST [(usp - 128, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)]
                 [e_stack_malloc 1%nat; e_returnErrorPtr; e_lept_stderr; e_kernelCreate; e_pixGetPixel; e_kernelSetElement; e_pixGetDimensions; 0x919f8; 0x918a8].
    idtac "F2-WALK".
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
    idtac "F3-ACC".
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch goal with MUx : munch ((usp - 128, usp) :: _) ?ma ?mb |- _ =>
      lazymatch goal with A : ART RT ?S ma |- _ =>
        assert (KL2 : keeps_live (rt_live RT S) ma mb)
          by (apply (keeps_live_walk1 RT AF S ma mb fr usp (usp - 128) A ltac:(rewrite FRS; left; reflexivity)
                       ltac:(repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; unfold STACK_WIN; lia) MUx)) end;
      assert (POBJ2 : pix_obj (rt_live RT Σ) mb pix v cv)
        by (apply (pix_obj_keep _ ma mb pix v cv); [| exact POBJ1];
            intros bb kk Hin; apply KL2; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact Hin) end.
    clear POBJ1.
    idtac "F3KL".
    (* [comment removed for export] *)
    lazymatch goal with MUx : munch _ ?mm _ |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                        repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
    idtac "F3-ART".
    walk_to AF MST [(usp - 256, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)]
                 [e_stack_malloc 1%nat; e_returnErrorPtr; e_lept_stderr; e_kernelCreate; e_pixGetPixel; e_kernelSetElement; 0x919f8; 0x918a8].
    idtac "F3-WALK".
    (* [comment removed for export] *)
    pose proof HOK as (HDIN & HWR & HHR & HWPL & HRS).
    assert (DR : 1 <= p_d v <= 32) by (clear - HDIN; cbn in HDIN; lia).
    rewrite !(sx32_small (p_d v)) by lia.
    destruct (Z.eq_dec (p_d v) 8) as [D8|DN8].
    { (* [comment removed for export] *)
      brF.
      awalk [e_stack_malloc 1%nat; e_returnErrorPtr; e_lept_stderr; e_kernelCreate; e_pixGetPixel; e_kernelSetElement; 0x919f8; 0x918a8].
      idtac "F4-WALK".
    (* [comment removed for export] *)
      rewrite !(sx32_small (p_h v)) by lia.
      destruct (Z_lt_le_dec 2 (p_h v)) as [HG3|HLE2].
      { brF.
        awalk [e_stack_malloc 1%nat; e_returnErrorPtr; e_lept_stderr; e_kernelCreate; e_pixGetPixel; e_kernelSetElement; 0x919f8; 0x918a8].
        idtac "F5-WALK".
    (* [comment removed for export] *)
        rewrite !(sx32_small (p_w v)) by lia.
        destruct (Z_lt_le_dec 2 (p_w v)) as [WG3|WLE2].
        { brF.
          awalk [e_stack_malloc 1%nat; e_returnErrorPtr; e_lept_stderr; e_kernelCreate; e_pixGetPixel; e_kernelSetElement; 0x919f8; 0x918a8].
          idtac "F6-WALK".
    (* [comment removed for export] *)
          assert (WH : p_w v * p_h v <= 2^26).
          { assert (W4 : p_w v <= 4 * p_wpl v) by (rewrite HWPL, D8; Z.div_mod_to_equations; lia). nia. }
          assert (WHN : 0 <= p_w v * p_h v) by nia.
          pose proof (km_cost_bound (p_h v) (p_w v) ltac:(lia) ltac:(lia) WH) as KCB.
    (* [comment removed for export] *)
          (* [comment removed for export] *)
          lazymatch goal with MUx : munch ((usp - 256, usp) :: _) ?ma ?mb |- _ =>
            lazymatch goal with A : ART RT ?S ma |- _ =>
              assert (KL3 : keeps_live (rt_live RT S) ma mb)
                by (apply (keeps_live_walk1 RT AF S ma mb fr usp (usp - 256) A
                             ltac:(repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; left; reflexivity)
                             ltac:(repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; unfold STACK_WIN; lia) MUx)) end;
            assert (POBJ3 : pix_obj (rt_live RT Σ) mb pix v cv)
              by (apply (pix_obj_keep _ ma mb pix v cv); [| exact POBJ2];
                  intros bb kk Hin; apply KL3; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact Hin) end.
          clear POBJ2.
          idtac "F7KL".
    (* [comment removed for export] *)
          at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                        ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                              repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
          idtac "F7-ATCALL".
          pose proof KCR as KC. unfold kernelCreate_cps in KC.
          eapply cps_seq.
          { eapply KC with (lo := lo) (h := p_h v) (w := p_w v); rt_side idtac.
            all: lazymatch goal with
                 | |- lenv _ _ _ _ _ _ => lenv_tac
                 | |- 3 <= _ <= 20000 => lia
                 | |- lres _ _ _ _ _ =>
                     unfold lres; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end;
                     repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end;
                     repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end; cbn [length];
                     split; [lia| split; [lia| split; [lia| exact LVP]]]
                 | |- sec_bytes _ + _ + _ <= _ => repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact (SECB D8)
                 | |- ?g => idtac "LEFT-KC:" g
                 end. }
          idtac "F7-CALL".
    (* [comment removed for export] *)
          after_call RT AF.
          idtac "F8-AFTER".
    (* [comment removed for export] *)
          (* [comment removed for export] *)
          lazymatch goal with AGx : agree_on _ ?ma ?mb, KO : kel_obj _ ?mb _ _ _ _ _ _ _ |- _ =>
            assert (POBJ4 : pix_obj (rt_live RT Σ) mb pix v cv)
              by (apply (pix_obj_keep _ ma mb pix v cv); [| exact POBJ3];
                  intros bb kk Hin a Ha; apply AGx; split;
                  [ right; right; left; exists bb, kk; split; [repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact Hin| exact Ha]
                  | exact I ]) end.
          clear POBJ3.
          idtac "F8KL".
    (* [comment removed for export] *)
          fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]| exact I]).
          idtac "F8-FOLD".
    (* [comment removed for export] *)
          lazymatch goal with H : kel_obj _ _ ?k _ _ _ _ ?d ?rs |- _ => rename k into kel; rename d into data; rename rs into rows; rename H into KOBJ end.
          lazymatch goal with H : rt_live RT ?S = km_live kel data _ _ rows _ |- _ => rename S into S1; rename H into LV1 end.
          lazymatch goal with A : ART RT S1 ?mm |- _ => rename mm into mk; rename A into ART1 end.
          pose proof KOBJ as (KCEL & (KIN & K0 & K16 & _) & DARR & (DIN & DD0 & DD16 & _) & RLEN & RFA & KND & SYB & SXB).
          unfold kel_cells in KCEL.
          assert (LVS : rt_live RT S1 = (rev (map (fun r => (r, 4 * p_w v)) rows) ++ [(data, 8 * p_h v)]) ++ (kel, 24) :: rt_live RT Σ).
          { rewrite LV1. repeat match goal with H : rt_live _ _ = rt_live RT Σ |- _ => rewrite H end. unfold km_live. rewrite <- app_assoc. reflexivity. }
          assert (KPX : kel + 24 <= pix \/ pix + 64 <= kel).
          { apply (af_live_disj RT AF S1 mk kel 24 pix 64 _ _ ART1 LVS). apply in_or_app. right. exact PIN. }
          assert (KDT : kel + 24 <= p_data v \/ p_data v + 4 * (p_wpl v * p_h v) <= kel).
          { apply (af_live_disj RT AF S1 mk kel 24 (p_data v) (4 * (p_wpl v * p_h v)) _ _ ART1 LVS). apply in_or_app. right. exact IND. }
          (* [comment removed for export] *)
          assert (FRS1 : rt_frames RT S1 = (fr, 1%nat) :: rt_frames RT Σ)
            by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity).
          pose proof (af_live_range RT AF S1 mk kel 24 ART1 KIN) as (_ & CKRk & CKSk).
          pose proof (gp_live_hi RT GP S1 mk kel 24 ART1 KIN) as CKHk.
          unfold STACK_WIN, SEGTOP_A in CKRk, CKSk.
          repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H in CKRk end.
          pose proof (af_frames_range RT AF S1 mk fr 1%nat ART1 ltac:(rewrite FRS1; left; reflexivity)) as (_ & _ & _ & FCDk).
          specialize (FCDk kel 24 KIN).
          pose proof (af_fshadow_apart RT AF S1 mk fr 1%nat ART1 ltac:(rewrite FRS1; left; reflexivity)) as (FCSk & _).
          specialize (FCSk kel 24 KIN). change (fs_size 1) with 128 in FCDk, FCSk. unfold shad, SHB in FCSk. norm_fshadow.
          refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
          idtac "F9-FACTS".
          walk_to AF MST [(usp - 128, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16); (kel, kel + 24)]
                       [e_stack_malloc 1%nat; e_returnErrorPtr; e_lept_stderr; e_kernelCreate; e_pixGetPixel; e_kernelSetElement; 0x919f8; 0x918a8].
          idtac "F9-WALK".
    (* [comment removed for export] *)
          pose proof (acc_live RT AF S1 mk kel 24 ART1 KIN) as ACCK.
          awalk [e_stack_malloc 1%nat; e_returnErrorPtr; e_lept_stderr; e_kernelCreate; e_pixGetPixel; e_kernelSetElement; 0x919f8; 0x918a8].
          idtac "F10-WALK".
    (* [comment removed for export] *)
          rewrite !(sx32_small (p_h v)) by lia. brF.
          awalk [e_stack_malloc 1%nat; e_returnErrorPtr; e_lept_stderr; e_kernelCreate; e_pixGetPixel; e_kernelSetElement; 0x919f8; 0x918a8].
          idtac "F11-WALK".
    (* [comment removed for export] *)
          rewrite !(sx32_small (p_w v)) by lia. brF.
          awalk [e_stack_malloc 1%nat; e_returnErrorPtr; e_lept_stderr; e_kernelCreate; e_pixGetPixel; e_kernelSetElement; 0x919f8; 0x918a8].
          idtac "F12-WALK".
    (* [comment removed for export] *)

          (* [comment removed for export] *)
          (* [comment removed for export] *)
          assert (KOLD : forall b kk, In (b, kk) (rt_live RT Σ) -> kel + 24 <= b \/ b + kk <= kel).
          { intros b kk Hb. apply (af_live_disj RT AF S1 mk kel 24 b kk _ _ ART1 LVS). apply in_or_app. right. exact Hb. }
          assert (KDA : kel + 24 <= data \/ data + 8 * p_h v <= kel).
          { apply (af_live_disj RT AF S1 mk kel 24 data (8 * p_h v) _ _ ART1 LVS). apply in_or_app. left. apply in_or_app. right. left. reflexivity. }
          lazymatch goal with MUx : munch ((usp - 128, usp) :: _) mk ?mb |- _ =>
            (* [comment removed for export] *)
            assert (KL5 : forall q n, In (q, n) (rt_live RT S1) -> (q + n <= kel \/ kel + 24 <= q) -> keeps_live [(q, n)] mk mb)
              by (intros q n Hq Hk bb kk Hin a Ha; destruct Hin as [Hin|[]]; injection Hin as <- <-; apply MUx;
                  pose proof (live_outside_walk1 RT AF S1 mk fr usp (usp - 128) q n (bv_unsigned a) ART1 ltac:(rewrite FRS1; left; reflexivity)
                                ltac:(repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; unfold STACK_WIN; lia) Hq Ha) as HO;
                  cbn [outside] in HO |- *; destruct HO as (O1 & O2 & O3 & _); repeat split; try exact I; first [exact O1 | exact O2 | exact O3 | lia]);
            assert (POBJ5 : pix_obj (rt_live RT Σ) mb pix v cv)
              by (apply (pix_obj_keep _ mk mb pix v cv); [| exact POBJ4];
                  intros bb kk Hin; apply (KL5 bb kk ltac:(rewrite LVS; apply in_or_app; right; right; exact Hin)
                                             ltac:(pose proof (KOLD bb kk Hin); lia) bb kk ltac:(left; reflexivity)));
            assert (KOBJ5 : kel_obj (rt_live RT S1) mb kel (p_h v) (p_w v) 2 2 data rows)
              by (apply (kel_obj_cells (rt_live RT S1) mk mb kel (p_h v) (p_w v) 0 0 2 2 data rows KOBJ); [unfold kel_cells; exact KCEL| | assumption];
                  intros a Ha; apply (KL5 data (8 * p_h v) DIN ltac:(lia) data (8 * p_h v) ltac:(left; reflexivity) a Ha))
          end.
          clear POBJ4.
          idtac "F13-OBJ".
    (* [comment removed for export] *)
          (* [comment removed for export] *)
          lazymatch goal with H : rw_cells _ _ fr (C8 _ :: _) |- _ => rename H into FRC end.
          rewrite (sx32_small (p_w v)) in FRC by lia. rewrite (sx32_small (p_h v)) in FRC by lia. rewrite (sx32_small (p_d v)) in FRC by lia.
          rewrite D8 in FRC.
          split_last_CB FRC [12%nat; 4%nat; 36%nat].
          lazymatch type of FRC with rw_cells _ ?mm _ (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: CB 4 ?bs :: ?post) =>
            destruct (cb4_c4_in mm fr [c1; c2; c3; c4; c5; c6; c7; c8; c9; c10] post bs FRC) as (xv & FRC2); clear FRC; cbn [app] in FRC2 end.
          split_at FRC2 10%nat FVAL. split_at FVAL 1%nat FHI.
          idtac "F14-CELLS".
    (* [comment removed for export] *)
          (* [comment removed for export] *)
          assert (KPF : forall z, PF z -> z < kel \/ kel + 24 <= z).
          { intros z Hz. unfold PF, aclient in Hz. unfold USTACK_TOP in Hz.
            pose proof (af_live_range RT AF S1 mk kel 24 ART1 KIN) as (_ & KR1 & KR2). unfold STACK_WIN, SEGTOP_A in KR1, KR2.
            repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H in KR1 end.
            destruct Hz as [Hs|[Hs|[Hs|[Hs|Hs]]]].
            - lia.
            - pose proof (client_static_below _ Hs). pose proof (client_static_ge _ Hs). unfold SEGTOP_A in *. lia.
            - destruct Hs as (b & kk & Hb & Hr). pose proof (KOLD b kk Hb). lia.
            - destruct Hs as (f & kf & Hf & Hr).
              pose proof (af_frames_range RT AF S1 mk f kf ART1 ltac:(rewrite FRS1; right; exact Hf)) as (_ & _ & _ & FLV').
              pose proof (FLV' kel 24 KIN). lia.
            - destruct Hs as (f & kf & Hf & Hr).
              pose proof (af_fshadow_apart RT AF S1 mk f kf ART1 ltac:(rewrite FRS1; right; exact Hf)) as (FS' & _).
              pose proof (FS' kel 24 KIN). lia. }
          idtac "F15-KPF".
          cps_stop.
          art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac|
                                split; [intros zz Hzz; right; right; left; exists kel, 24; split; [solve [eassumption | rewrite LVS; apply in_or_app; right; left; reflexivity]| lia]| exact I]]]]).
          idtac "F15-ART".
          lazymatch goal with MUx : munch _ ?mm _ |- _ =>
            agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; pose proof (KPF _ Hx) as N3; unfold shad, SHB in *;
                                              repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
          idtac "F15-AGF".
          to_entry.
          idtac "F15-ENTRY".
    (* [comment removed for export] *)

          pose proof (kfp_loop_ok_0 RT AF RC GP GPX (kernelSetElement_obj_ok RT AF KSE) Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m pix v cv fr
                       (kfp_exit_ok_0 RT AF RC GP Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m pix v cv fr)) as LOOP.
          eapply cps_conseq; [exact (LOOP 0 ltac:(nia))| | intros c Hc; exact Hc].
          intros c Hc. unfold kfp_head_0. do 33 eexists. split; [exact Hc|].
          idtac "F16-HC".
          split; [lia|]. split; [lia|]. split; [lia|].
          split.
          { split; [| split; [exact D8| split; [exact HOK| split; [lia| split; [lia| split; [exact WH| split; [exact LVB| exact CRB]]]]]]].
            assert (LO0 : 0 <= lo) by lia.
            exact (conj FDO (conj MST (conj ART0 (conj POBJ (conj LOW (conj LOR (conj LO0 (conj SPT (conj SPA (conj SPB
                     (conj LVP (conj FRB (conj DNZ (conj FR0 (conj FR64 NFA))))))))))))))). }
          idtac "F16-LCTX".
    (* [comment removed for export] *)
          split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
          idtac "F17-A".
          split; [unfold kfp_stack_0; exact FR|].
          split; [unfold kfp_frame_lo; exact FRC2|].
          split; [exact FVAL|]. split; [exact FHI|].
          split; [unfold kfp_fshadow; exact FSH|].
          idtac "F17-B".
          split; [eassumption|]. split; [eassumption|]. split; [exact AGF|]. split; [exact POBJ5|].
          split; [exact KOBJ5|].
          idtac "F17-C".
          split; [rewrite LV1; repeat match goal with H : rt_live RT ?X = rt_live RT ?Y |- context [rt_live RT ?X] => rewrite H end; reflexivity|].
          split; [exact FRS1|].
          split; [repeat match goal with H : rt_sp0 RT ?X = rt_sp0 RT ?Y |- context [rt_sp0 RT ?X] => rewrite H end; reflexivity|].
          lia.
    (* [comment removed for export] *)
        }
        { (* [comment removed for export] *)
          brT.
          awalk [e_stack_malloc 1%nat; e_returnErrorPtr; e_lept_stderr; e_kernelCreate; e_pixGetPixel; e_kernelSetElement; 0x919f8; 0x918a8].
          idtac "F18-LEAF".
    (* [comment removed for export] *)
          (* [comment removed for export] *)
          lazymatch goal with MUx : munch ((usp - 256, usp) :: _) ?ma ?mb |- _ =>
            lazymatch goal with A : ART RT ?S ma |- _ =>
              assert (KL3 : keeps_live (rt_live RT S) ma mb)
                by (apply (keeps_live_walk1 RT AF S ma mb fr usp (usp - 256) A
                             ltac:(repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; left; reflexivity)
                             ltac:(repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; unfold STACK_WIN; lia) MUx)) end;
            assert (POBJ3 : pix_obj (rt_live RT Σ) mb pix v cv)
              by (apply (pix_obj_keep _ ma mb pix v cv); [| exact POBJ2];
                  intros bb kk Hin; apply KL3; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact Hin) end.
          clear POBJ2.
          at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                        ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                              repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
          pose proof RERR as RE. unfold returnError_cps in RE.
          eapply cps_seq; [eapply RE with (lo := lo); rt_side idtac; [lit_in | lit_in | lenv_tac | lres_tac..] |].
          idtac "F19-CALL".
          after_call RT AF.
          lazymatch goal with AGx : agree_on _ ?ma ?mb |- cps _ (ASTA RT _ _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
            assert (POBJ4 : pix_obj (rt_live RT Σ) mb pix v cv)
              by (apply (pix_obj_keep _ ma mb pix v cv); [| exact POBJ3];
                  intros bb kk Hin a Ha; apply AGx;
                  right; right; left; exists bb, kk; split; [repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact Hin| exact Ha]) end.
          clear POBJ3.
          fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]).
          idtac "F19-AFTER".
    (* [comment removed for export] *)
          refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
          walk_to AF MST [(usp - 256, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)]
                       [e_stack_malloc 1%nat; e_returnErrorPtr; e_lept_stderr; e_kernelCreate; e_pixGetPixel; e_kernelSetElement; 0x919f8; 0x918a8].
          lazymatch goal with MUx : munch ((usp - 256, usp) :: _) ?ma ?mb |- _ =>
            lazymatch goal with A : ART RT ?S ma |- _ =>
              assert (KL6 : keeps_live (rt_live RT S) ma mb)
                by (apply (keeps_live_walk1 RT AF S ma mb fr usp (usp - 256) A
                             ltac:(repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; left; reflexivity)
                             ltac:(repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; unfold STACK_WIN; lia) MUx)) end;
            assert (POBJ5 : pix_obj (rt_live RT Σ) mb pix v cv)
              by (apply (pix_obj_keep _ ma mb pix v cv); [| exact POBJ4];
                  intros bb kk Hin; apply KL6; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact Hin) end.
          clear POBJ4.
          cps_stop.
          art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
          lazymatch goal with MUx : munch _ ?mm _ |- _ =>
            agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                              repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
          to_entry.
          idtac "F20-EXITSTATE".
    (* [comment removed for export] *)
          pose proof (kfp_exit_ok_0 RT AF RC GP Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m pix v cv fr) as EXITs.
          assert (CTXk : kfp_ctx RT Σ PMc usp lo m pix v cv fr).
          { assert (LO0 : 0 <= lo) by lia.
            exact (conj FDO (conj MST (conj ART0 (conj POBJ (conj LOW (conj LOR (conj LO0 (conj SPT (conj SPA (conj SPB
                     (conj LVP (conj FRB (conj DNZ (conj FR0 (conj FR64 NFA))))))))))))))). }
          lazymatch goal with |- cps _ (ASTA RT ?S _ (eq (entry_st ?a1 _ _ _ ?a5 ?a6 ?a7 _ _ ?a10 ?a11 ?a12 ?a13 ?a14 ?a15 ?a16 ?a17 _ ?a19 _ ?a21 ?a22 ?a23 ?a24 ?a25 _ _ ?a28 ?a29 ?a30 ?a31 ?FF ?fcc _ ?mm))) _ =>
            eapply (cps_conseq _ _ _ _ _ (EXITs S mm 0 (Z_to_bv 64 1102416563)
                                  _ _
                                  a1 a5 a6 a7 a10 a11 a12 a13 a14 a15 a16 a17 a19 a21 a22 a23 a24 a25 a28 a29 a30 a31 FF fcc CTXk
                                  ltac:(eassumption) ltac:(eassumption) ltac:(eassumption) ltac:(eassumption)
                                  ltac:(unfold kfp_stack_0; exact FR)
                                  ltac:(lazymatch goal with H : rw_cells _ _ fr (C8 _ :: _) |- _ => exact (rw_cells_head _ _ _ _ H) end)
                                  ltac:(unfold kfp_fshadow; exact FSH)
                                  ltac:(eassumption) ltac:(eassumption) AGF _ _ _ _ _))
          end.
          Unshelve.
    (* [comment removed for export] *)
          1: (intros c Hc; exact Hc).
          1: (intros c Hc; exact Hc).
          1: (repeat match goal with H : rt_frames RT ?X = rt_frames RT ?Y |- context [rt_frames RT ?X] => rewrite H end; first [exact FRS | reflexivity]).
          1: (repeat match goal with H : rt_sp0 RT ?X = rt_sp0 RT ?Y |- context [rt_sp0 RT ?X] => rewrite H end; reflexivity).
          1: (repeat match goal with H : rt_credit RT ?X = _ |- context [rt_credit RT ?X] => rewrite H end; lia).
          1: (apply (km_pix_obj_mono (rt_live RT Σ)); [| exact POBJ5]; intros e He;
              repeat match goal with H : rt_live RT ?X = rt_live RT ?Y |- context [rt_live RT ?X] => rewrite H end; exact He).
          1: (left; split; [reflexivity|]; repeat match goal with H : rt_live RT ?X = rt_live RT ?Y |- context [rt_live RT ?X] => rewrite H end; reflexivity).
    (* [comment removed for export] *)
        }
      }
      { (* [comment removed for export] *)
        brT.
        awalk [e_stack_malloc 1%nat; e_returnErrorPtr; e_lept_stderr; e_kernelCreate; e_pixGetPixel; e_kernelSetElement; 0x919f8; 0x918a8].
        idtac "F23-LEAF".
    (* [comment removed for export] *)
          (* [comment removed for export] *)
          lazymatch goal with MUx : munch ((usp - 256, usp) :: _) ?ma ?mb |- _ =>
            lazymatch goal with A : ART RT ?S ma |- _ =>
              assert (KL3 : keeps_live (rt_live RT S) ma mb)
                by (apply (keeps_live_walk1 RT AF S ma mb fr usp (usp - 256) A
                             ltac:(repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; left; reflexivity)
                             ltac:(repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; unfold STACK_WIN; lia) MUx)) end;
            assert (POBJ3 : pix_obj (rt_live RT Σ) mb pix v cv)
              by (apply (pix_obj_keep _ ma mb pix v cv); [| exact POBJ2];
                  intros bb kk Hin; apply KL3; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact Hin) end.
          clear POBJ2.
          at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                        ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                              repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
          pose proof RERR as RE. unfold returnError_cps in RE.
          eapply cps_seq; [eapply RE with (lo := lo); rt_side idtac; [lit_in | lit_in | lenv_tac | lres_tac..] |].
          idtac "F19-CALL".
          after_call RT AF.
          lazymatch goal with AGx : agree_on _ ?ma ?mb |- cps _ (ASTA RT _ _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
            assert (POBJ4 : pix_obj (rt_live RT Σ) mb pix v cv)
              by (apply (pix_obj_keep _ ma mb pix v cv); [| exact POBJ3];
                  intros bb kk Hin a Ha; apply AGx;
                  right; right; left; exists bb, kk; split; [repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact Hin| exact Ha]) end.
          clear POBJ3.
          fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]).
          idtac "F19-AFTER".
    (* [comment removed for export] *)
          refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
          walk_to AF MST [(usp - 256, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)]
                       [e_stack_malloc 1%nat; e_returnErrorPtr; e_lept_stderr; e_kernelCreate; e_pixGetPixel; e_kernelSetElement; 0x919f8; 0x918a8].
          lazymatch goal with MUx : munch ((usp - 256, usp) :: _) ?ma ?mb |- _ =>
            lazymatch goal with A : ART RT ?S ma |- _ =>
              assert (KL6 : keeps_live (rt_live RT S) ma mb)
                by (apply (keeps_live_walk1 RT AF S ma mb fr usp (usp - 256) A
                             ltac:(repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; left; reflexivity)
                             ltac:(repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; unfold STACK_WIN; lia) MUx)) end;
            assert (POBJ5 : pix_obj (rt_live RT Σ) mb pix v cv)
              by (apply (pix_obj_keep _ ma mb pix v cv); [| exact POBJ4];
                  intros bb kk Hin; apply KL6; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact Hin) end.
          clear POBJ4.
          cps_stop.
          art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
          lazymatch goal with MUx : munch _ ?mm _ |- _ =>
            agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                              repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
          to_entry.
          idtac "F20-EXITSTATE".
    (* [comment removed for export] *)
          pose proof (kfp_exit_ok_0 RT AF RC GP Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m pix v cv fr) as EXITs.
          assert (CTXk : kfp_ctx RT Σ PMc usp lo m pix v cv fr).
          { assert (LO0 : 0 <= lo) by lia.
            exact (conj FDO (conj MST (conj ART0 (conj POBJ (conj LOW (conj LOR (conj LO0 (conj SPT (conj SPA (conj SPB
                     (conj LVP (conj FRB (conj DNZ (conj FR0 (conj FR64 NFA))))))))))))))). }
          lazymatch goal with |- cps _ (ASTA RT ?S _ (eq (entry_st ?a1 _ _ _ ?a5 ?a6 ?a7 _ _ ?a10 ?a11 ?a12 ?a13 ?a14 ?a15 ?a16 ?a17 _ ?a19 _ ?a21 ?a22 ?a23 ?a24 ?a25 _ _ ?a28 ?a29 ?a30 ?a31 ?FF ?fcc _ ?mm))) _ =>
            eapply (cps_conseq _ _ _ _ _ (EXITs S mm 0 (Z_to_bv 64 1102416563)
                                  _ _
                                  a1 a5 a6 a7 a10 a11 a12 a13 a14 a15 a16 a17 a19 a21 a22 a23 a24 a25 a28 a29 a30 a31 FF fcc CTXk
                                  ltac:(eassumption) ltac:(eassumption) ltac:(eassumption) ltac:(eassumption)
                                  ltac:(unfold kfp_stack_0; exact FR)
                                  ltac:(lazymatch goal with H : rw_cells _ _ fr (C8 _ :: _) |- _ => exact (rw_cells_head _ _ _ _ H) end)
                                  ltac:(unfold kfp_fshadow; exact FSH)
                                  ltac:(eassumption) ltac:(eassumption) AGF _ _ _ _ _))
          end.
          Unshelve.
    (* [comment removed for export] *)
          1: (intros c Hc; exact Hc).
          1: (intros c Hc; exact Hc).
          1: (repeat match goal with H : rt_frames RT ?X = rt_frames RT ?Y |- context [rt_frames RT ?X] => rewrite H end; first [exact FRS | reflexivity]).
          1: (repeat match goal with H : rt_sp0 RT ?X = rt_sp0 RT ?Y |- context [rt_sp0 RT ?X] => rewrite H end; reflexivity).
          1: (repeat match goal with H : rt_credit RT ?X = _ |- context [rt_credit RT ?X] => rewrite H end; lia).
          1: (apply (km_pix_obj_mono (rt_live RT Σ)); [| exact POBJ5]; intros e He;
              repeat match goal with H : rt_live RT ?X = rt_live RT ?Y |- context [rt_live RT ?X] => rewrite H end; exact He).
          1: (left; split; [reflexivity|]; repeat match goal with H : rt_live RT ?X = rt_live RT ?Y |- context [rt_live RT ?X] => rewrite H end; reflexivity).
    (* [comment removed for export] *)
      }
    }
    { (* [comment removed for export] *)
      brT.
      awalk [e_stack_malloc 1%nat; e_returnErrorPtr; e_lept_stderr; e_kernelCreate; e_pixGetPixel; e_kernelSetElement; 0x919f8; 0x918a8].
      idtac "F24-LEAF".
    (* [comment removed for export] *)
          (* [comment removed for export] *)
          lazymatch goal with MUx : munch ((usp - 256, usp) :: _) ?ma ?mb |- _ =>
            lazymatch goal with A : ART RT ?S ma |- _ =>
              assert (KL3 : keeps_live (rt_live RT S) ma mb)
                by (apply (keeps_live_walk1 RT AF S ma mb fr usp (usp - 256) A
                             ltac:(repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; left; reflexivity)
                             ltac:(repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; unfold STACK_WIN; lia) MUx)) end;
            assert (POBJ3 : pix_obj (rt_live RT Σ) mb pix v cv)
              by (apply (pix_obj_keep _ ma mb pix v cv); [| exact POBJ2];
                  intros bb kk Hin; apply KL3; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact Hin) end.
          clear POBJ2.
          at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                        ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                              repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
          pose proof RERR as RE. unfold returnError_cps in RE.
          eapply cps_seq; [eapply RE with (lo := lo); rt_side idtac; [lit_in | lit_in | lenv_tac | lres_tac..] |].
          idtac "F19-CALL".
          after_call RT AF.
          lazymatch goal with AGx : agree_on _ ?ma ?mb |- cps _ (ASTA RT _ _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
            assert (POBJ4 : pix_obj (rt_live RT Σ) mb pix v cv)
              by (apply (pix_obj_keep _ ma mb pix v cv); [| exact POBJ3];
                  intros bb kk Hin a Ha; apply AGx;
                  right; right; left; exists bb, kk; split; [repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact Hin| exact Ha]) end.
          clear POBJ3.
          fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]).
          idtac "F19-AFTER".
    (* [comment removed for export] *)
          refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
          walk_to AF MST [(usp - 256, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)]
                       [e_stack_malloc 1%nat; e_returnErrorPtr; e_lept_stderr; e_kernelCreate; e_pixGetPixel; e_kernelSetElement; 0x919f8; 0x918a8].
          lazymatch goal with MUx : munch ((usp - 256, usp) :: _) ?ma ?mb |- _ =>
            lazymatch goal with A : ART RT ?S ma |- _ =>
              assert (KL6 : keeps_live (rt_live RT S) ma mb)
                by (apply (keeps_live_walk1 RT AF S ma mb fr usp (usp - 256) A
                             ltac:(repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; left; reflexivity)
                             ltac:(repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; unfold STACK_WIN; lia) MUx)) end;
            assert (POBJ5 : pix_obj (rt_live RT Σ) mb pix v cv)
              by (apply (pix_obj_keep _ ma mb pix v cv); [| exact POBJ4];
                  intros bb kk Hin; apply KL6; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact Hin) end.
          clear POBJ4.
          cps_stop.
          art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
          lazymatch goal with MUx : munch _ ?mm _ |- _ =>
            agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                              repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
          to_entry.
          idtac "F20-EXITSTATE".
    (* [comment removed for export] *)
          pose proof (kfp_exit_ok_0 RT AF RC GP Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m pix v cv fr) as EXITs.
          assert (CTXk : kfp_ctx RT Σ PMc usp lo m pix v cv fr).
          { assert (LO0 : 0 <= lo) by lia.
            exact (conj FDO (conj MST (conj ART0 (conj POBJ (conj LOW (conj LOR (conj LO0 (conj SPT (conj SPA (conj SPB
                     (conj LVP (conj FRB (conj DNZ (conj FR0 (conj FR64 NFA))))))))))))))). }
          lazymatch goal with |- cps _ (ASTA RT ?S _ (eq (entry_st ?a1 _ _ _ ?a5 ?a6 ?a7 _ _ ?a10 ?a11 ?a12 ?a13 ?a14 ?a15 ?a16 ?a17 _ ?a19 _ ?a21 ?a22 ?a23 ?a24 ?a25 _ _ ?a28 ?a29 ?a30 ?a31 ?FF ?fcc _ ?mm))) _ =>
            eapply (cps_conseq _ _ _ _ _ (EXITs S mm 0 (Z_to_bv 64 1102416563)
                                  _ _
                                  a1 a5 a6 a7 a10 a11 a12 a13 a14 a15 a16 a17 a19 a21 a22 a23 a24 a25 a28 a29 a30 a31 FF fcc CTXk
                                  ltac:(eassumption) ltac:(eassumption) ltac:(eassumption) ltac:(eassumption)
                                  ltac:(unfold kfp_stack_0; exact FR)
                                  ltac:(lazymatch goal with H : rw_cells _ _ fr (C8 _ :: _) |- _ => exact (rw_cells_head _ _ _ _ H) end)
                                  ltac:(unfold kfp_fshadow; exact FSH)
                                  ltac:(eassumption) ltac:(eassumption) AGF _ _ _ _ _))
          end.
          Unshelve.
    (* [comment removed for export] *)
          1: (intros c Hc; exact Hc).
          1: (intros c Hc; exact Hc).
          1: (repeat match goal with H : rt_frames RT ?X = rt_frames RT ?Y |- context [rt_frames RT ?X] => rewrite H end; first [exact FRS | reflexivity]).
          1: (repeat match goal with H : rt_sp0 RT ?X = rt_sp0 RT ?Y |- context [rt_sp0 RT ?X] => rewrite H end; reflexivity).
          1: (repeat match goal with H : rt_credit RT ?X = _ |- context [rt_credit RT ?X] => rewrite H end; lia).
          1: (apply (km_pix_obj_mono (rt_live RT Σ)); [| exact POBJ5]; intros e He;
              repeat match goal with H : rt_live RT ?X = rt_live RT ?Y |- context [rt_live RT ?X] => rewrite H end; exact He).
          1: (left; split; [reflexivity|]; repeat match goal with H : rt_live RT ?X = rt_live RT ?Y |- context [rt_live RT ?X] => rewrite H end; reflexivity).
    (* [comment removed for export] *)
    }

  - (* [comment removed for export] *)
    carve_frame 144%nat ST.
    (* [comment removed for export] *)
    walk_to AF MST [(usp - 144, usp)] [e_stack_malloc 1%nat; e_returnErrorPtr; e_lept_stderr; e_kernelCreate; e_pixGetPixel; e_kernelSetElement; 0x919f8; 0x918a8].
    idtac "F1-WALK".
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
    eapply cps_seq.
    { pose proof (gp_stack_malloc_1 RT GP) as SM0; unfold stack_malloc_contract' in SM0; eapply SM0 with (lo := lo); rt_side idtac. }
    after_call RT AF.
    fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]).
    fframe_open RT AF PF (rt_live RT Σ) usp 1%nat 128 ltac:(fun Ha => exact Ha).
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
    idtac "F1-FRAME".
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch goal with |- cps _ (ASTA RT ?S _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
      assert (KL0 : keeps_live (rt_live RT Σ) m mb)
        by (intros bb kk Hin a Ha; apply AGF; right; right; left; exists bb, kk; split; [exact Hin| exact Ha]);
      pose proof (pix_obj_keep _ m mb pix v cv KL0 POBJ) as POBJ1 end.
    pose proof POBJ1 as (PXC1 & _). unfold pix_cells in PXC1.
    chunk_facts RT AF GP pix 64.
    chunk_facts RT AF GP (p_data v) (4 * (p_wpl v * p_h v)).
    fframe_chunk RT AF fr 1%nat 128 pix 64. norm_fshadow.
    walk_to AF MST [(usp - 144, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)]
                 [e_stack_malloc 1%nat; e_returnErrorPtr; e_lept_stderr; e_kernelCreate; e_pixGetPixel; e_kernelSetElement; e_pixGetDimensions; 0x919f8; 0x918a8].
    idtac "F2-WALK".
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
    idtac "F3-ACC".
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch goal with MUx : munch ((usp - 144, usp) :: _) ?ma ?mb |- _ =>
      lazymatch goal with A : ART RT ?S ma |- _ =>
        assert (KL2 : keeps_live (rt_live RT S) ma mb)
          by (apply (keeps_live_walk1 RT AF S ma mb fr usp (usp - 144) A ltac:(rewrite FRS; left; reflexivity)
                       ltac:(repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; unfold STACK_WIN; lia) MUx)) end;
      assert (POBJ2 : pix_obj (rt_live RT Σ) mb pix v cv)
        by (apply (pix_obj_keep _ ma mb pix v cv); [| exact POBJ1];
            intros bb kk Hin; apply KL2; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact Hin) end.
    clear POBJ1.
    idtac "F3KL".
    (* [comment removed for export] *)
    lazymatch goal with MUx : munch _ ?mm _ |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                        repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
    idtac "F3-ART".
    walk_to AF MST [(usp - 256, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)]
                 [e_stack_malloc 1%nat; e_returnErrorPtr; e_lept_stderr; e_kernelCreate; e_pixGetPixel; e_kernelSetElement; 0x919f8; 0x918a8].
    idtac "F3-WALK".
    (* [comment removed for export] *)
    pose proof HOK as (HDIN & HWR & HHR & HWPL & HRS).
    assert (DR : 1 <= p_d v <= 32) by (clear - HDIN; cbn in HDIN; lia).
    rewrite !(sx32_small (p_d v)) by lia.
    destruct (Z.eq_dec (p_d v) 8) as [D8|DN8].
    { (* [comment removed for export] *)
      brF.
      awalk [e_stack_malloc 1%nat; e_returnErrorPtr; e_lept_stderr; e_kernelCreate; e_pixGetPixel; e_kernelSetElement; 0x919f8; 0x918a8].
      idtac "F4-WALK".
    (* [comment removed for export] *)
      rewrite !(sx32_small (p_h v)) by lia.
      destruct (Z_lt_le_dec 2 (p_h v)) as [HG3|HLE2].
      { brF.
        awalk [e_stack_malloc 1%nat; e_returnErrorPtr; e_lept_stderr; e_kernelCreate; e_pixGetPixel; e_kernelSetElement; 0x919f8; 0x918a8].
        idtac "F5-WALK".
    (* [comment removed for export] *)
        rewrite !(sx32_small (p_w v)) by lia.
        destruct (Z_lt_le_dec 2 (p_w v)) as [WG3|WLE2].
        { brF.
          awalk [e_stack_malloc 1%nat; e_returnErrorPtr; e_lept_stderr; e_kernelCreate; e_pixGetPixel; e_kernelSetElement; 0x919f8; 0x918a8].
          idtac "F6-WALK".
    (* [comment removed for export] *)
          assert (WH : p_w v * p_h v <= 2^26).
          { assert (W4 : p_w v <= 4 * p_wpl v) by (rewrite HWPL, D8; Z.div_mod_to_equations; lia). nia. }
          assert (WHN : 0 <= p_w v * p_h v) by nia.
          pose proof (km_cost_bound (p_h v) (p_w v) ltac:(lia) ltac:(lia) WH) as KCB.
    (* [comment removed for export] *)
          (* [comment removed for export] *)
          lazymatch goal with MUx : munch ((usp - 256, usp) :: _) ?ma ?mb |- _ =>
            lazymatch goal with A : ART RT ?S ma |- _ =>
              assert (KL3 : keeps_live (rt_live RT S) ma mb)
                by (apply (keeps_live_walk1 RT AF S ma mb fr usp (usp - 256) A
                             ltac:(repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; left; reflexivity)
                             ltac:(repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; unfold STACK_WIN; lia) MUx)) end;
            assert (POBJ3 : pix_obj (rt_live RT Σ) mb pix v cv)
              by (apply (pix_obj_keep _ ma mb pix v cv); [| exact POBJ2];
                  intros bb kk Hin; apply KL3; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact Hin) end.
          clear POBJ2.
          idtac "F7KL".
    (* [comment removed for export] *)
          at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                        ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                              repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
          idtac "F7-ATCALL".
          pose proof KCR as KC. unfold kernelCreate_cps in KC.
          eapply cps_seq.
          { eapply KC with (lo := lo) (h := p_h v) (w := p_w v); rt_side idtac.
            all: lazymatch goal with
                 | |- lenv _ _ _ _ _ _ => lenv_tac
                 | |- 3 <= _ <= 20000 => lia
                 | |- lres _ _ _ _ _ =>
                     unfold lres; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end;
                     repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end;
                     repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end; cbn [length];
                     split; [lia| split; [lia| split; [lia| exact LVP]]]
                 | |- sec_bytes _ + _ + _ <= _ => repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact (SECB D8)
                 | |- ?g => idtac "LEFT-KC:" g
                 end. }
          idtac "F7-CALL".
    (* [comment removed for export] *)
          after_call RT AF.
          idtac "F8-AFTER".
    (* [comment removed for export] *)
          (* [comment removed for export] *)
          lazymatch goal with AGx : agree_on _ ?ma ?mb, KO : kel_obj _ ?mb _ _ _ _ _ _ _ |- _ =>
            assert (POBJ4 : pix_obj (rt_live RT Σ) mb pix v cv)
              by (apply (pix_obj_keep _ ma mb pix v cv); [| exact POBJ3];
                  intros bb kk Hin a Ha; apply AGx; split;
                  [ right; right; left; exists bb, kk; split; [repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact Hin| exact Ha]
                  | exact I ]) end.
          clear POBJ3.
          idtac "F8KL".
    (* [comment removed for export] *)
          fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]| exact I]).
          idtac "F8-FOLD".
    (* [comment removed for export] *)
          lazymatch goal with H : kel_obj _ _ ?k _ _ _ _ ?d ?rs |- _ => rename k into kel; rename d into data; rename rs into rows; rename H into KOBJ end.
          lazymatch goal with H : rt_live RT ?S = km_live kel data _ _ rows _ |- _ => rename S into S1; rename H into LV1 end.
          lazymatch goal with A : ART RT S1 ?mm |- _ => rename mm into mk; rename A into ART1 end.
          pose proof KOBJ as (KCEL & (KIN & K0 & K16 & _) & DARR & (DIN & DD0 & DD16 & _) & RLEN & RFA & KND & SYB & SXB).
          unfold kel_cells in KCEL.
          assert (LVS : rt_live RT S1 = (rev (map (fun r => (r, 4 * p_w v)) rows) ++ [(data, 8 * p_h v)]) ++ (kel, 24) :: rt_live RT Σ).
          { rewrite LV1. repeat match goal with H : rt_live _ _ = rt_live RT Σ |- _ => rewrite H end. unfold km_live. rewrite <- app_assoc. reflexivity. }
          assert (KPX : kel + 24 <= pix \/ pix + 64 <= kel).
          { apply (af_live_disj RT AF S1 mk kel 24 pix 64 _ _ ART1 LVS). apply in_or_app. right. exact PIN. }
          assert (KDT : kel + 24 <= p_data v \/ p_data v + 4 * (p_wpl v * p_h v) <= kel).
          { apply (af_live_disj RT AF S1 mk kel 24 (p_data v) (4 * (p_wpl v * p_h v)) _ _ ART1 LVS). apply in_or_app. right. exact IND. }
          (* [comment removed for export] *)
          assert (FRS1 : rt_frames RT S1 = (fr, 1%nat) :: rt_frames RT Σ)
            by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity).
          pose proof (af_live_range RT AF S1 mk kel 24 ART1 KIN) as (_ & CKRk & CKSk).
          pose proof (gp_live_hi RT GP S1 mk kel 24 ART1 KIN) as CKHk.
          unfold STACK_WIN, SEGTOP_A in CKRk, CKSk.
          repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H in CKRk end.
          pose proof (af_frames_range RT AF S1 mk fr 1%nat ART1 ltac:(rewrite FRS1; left; reflexivity)) as (_ & _ & _ & FCDk).
          specialize (FCDk kel 24 KIN).
          pose proof (af_fshadow_apart RT AF S1 mk fr 1%nat ART1 ltac:(rewrite FRS1; left; reflexivity)) as (FCSk & _).
          specialize (FCSk kel 24 KIN). change (fs_size 1) with 128 in FCDk, FCSk. unfold shad, SHB in FCSk. norm_fshadow.
          refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
          idtac "F9-FACTS".
          walk_to AF MST [(usp - 144, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16); (kel, kel + 24)]
                       [e_stack_malloc 1%nat; e_returnErrorPtr; e_lept_stderr; e_kernelCreate; e_pixGetPixel; e_kernelSetElement; 0x919f8; 0x918a8].
          idtac "F9-WALK".
    (* [comment removed for export] *)
          pose proof (acc_live RT AF S1 mk kel 24 ART1 KIN) as ACCK.
          awalk [e_stack_malloc 1%nat; e_returnErrorPtr; e_lept_stderr; e_kernelCreate; e_pixGetPixel; e_kernelSetElement; 0x919f8; 0x918a8].
          idtac "F10-WALK".
    (* [comment removed for export] *)
          rewrite !(sx32_small (p_h v)) by lia. brF.
          awalk [e_stack_malloc 1%nat; e_returnErrorPtr; e_lept_stderr; e_kernelCreate; e_pixGetPixel; e_kernelSetElement; 0x919f8; 0x918a8].
          idtac "F11-WALK".
    (* [comment removed for export] *)
          rewrite !(sx32_small (p_w v)) by lia. brF.
          awalk [e_stack_malloc 1%nat; e_returnErrorPtr; e_lept_stderr; e_kernelCreate; e_pixGetPixel; e_kernelSetElement; 0x919f8; 0x918a8].
          idtac "F12-WALK".
    (* [comment removed for export] *)

          (* [comment removed for export] *)
          (* [comment removed for export] *)
          assert (KOLD : forall b kk, In (b, kk) (rt_live RT Σ) -> kel + 24 <= b \/ b + kk <= kel).
          { intros b kk Hb. apply (af_live_disj RT AF S1 mk kel 24 b kk _ _ ART1 LVS). apply in_or_app. right. exact Hb. }
          assert (KDA : kel + 24 <= data \/ data + 8 * p_h v <= kel).
          { apply (af_live_disj RT AF S1 mk kel 24 data (8 * p_h v) _ _ ART1 LVS). apply in_or_app. left. apply in_or_app. right. left. reflexivity. }
          lazymatch goal with MUx : munch ((usp - 144, usp) :: _) mk ?mb |- _ =>
            (* [comment removed for export] *)
            assert (KL5 : forall q n, In (q, n) (rt_live RT S1) -> (q + n <= kel \/ kel + 24 <= q) -> keeps_live [(q, n)] mk mb)
              by (intros q n Hq Hk bb kk Hin a Ha; destruct Hin as [Hin|[]]; injection Hin as <- <-; apply MUx;
                  pose proof (live_outside_walk1 RT AF S1 mk fr usp (usp - 144) q n (bv_unsigned a) ART1 ltac:(rewrite FRS1; left; reflexivity)
                                ltac:(repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; unfold STACK_WIN; lia) Hq Ha) as HO;
                  cbn [outside] in HO |- *; destruct HO as (O1 & O2 & O3 & _); repeat split; try exact I; first [exact O1 | exact O2 | exact O3 | lia]);
            assert (POBJ5 : pix_obj (rt_live RT Σ) mb pix v cv)
              by (apply (pix_obj_keep _ mk mb pix v cv); [| exact POBJ4];
                  intros bb kk Hin; apply (KL5 bb kk ltac:(rewrite LVS; apply in_or_app; right; right; exact Hin)
                                             ltac:(pose proof (KOLD bb kk Hin); lia) bb kk ltac:(left; reflexivity)));
            assert (KOBJ5 : kel_obj (rt_live RT S1) mb kel (p_h v) (p_w v) 2 2 data rows)
              by (apply (kel_obj_cells (rt_live RT S1) mk mb kel (p_h v) (p_w v) 0 0 2 2 data rows KOBJ); [unfold kel_cells; exact KCEL| | assumption];
                  intros a Ha; apply (KL5 data (8 * p_h v) DIN ltac:(lia) data (8 * p_h v) ltac:(left; reflexivity) a Ha))
          end.
          clear POBJ4.
          idtac "F13-OBJ".
    (* [comment removed for export] *)
          (* [comment removed for export] *)
          lazymatch goal with H : rw_cells _ _ fr (C8 _ :: _) |- _ => rename H into FRC end.
          rewrite (sx32_small (p_w v)) in FRC by lia. rewrite (sx32_small (p_h v)) in FRC by lia. rewrite (sx32_small (p_d v)) in FRC by lia.
          rewrite D8 in FRC.
          split_last_CB FRC [12%nat; 4%nat; 36%nat].
          lazymatch type of FRC with rw_cells _ ?mm _ (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: CB 4 ?bs :: ?post) =>
            destruct (cb4_c4_in mm fr [c1; c2; c3; c4; c5; c6; c7; c8; c9; c10] post bs FRC) as (xv & FRC2); clear FRC; cbn [app] in FRC2 end.
          split_at FRC2 10%nat FVAL. split_at FVAL 1%nat FHI.
          idtac "F14-CELLS".
    (* [comment removed for export] *)
          (* [comment removed for export] *)
          assert (KPF : forall z, PF z -> z < kel \/ kel + 24 <= z).
          { intros z Hz. unfold PF, aclient in Hz. unfold USTACK_TOP in Hz.
            pose proof (af_live_range RT AF S1 mk kel 24 ART1 KIN) as (_ & KR1 & KR2). unfold STACK_WIN, SEGTOP_A in KR1, KR2.
            repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H in KR1 end.
            destruct Hz as [Hs|[Hs|[Hs|[Hs|Hs]]]].
            - lia.
            - pose proof (client_static_below _ Hs). pose proof (client_static_ge _ Hs). unfold SEGTOP_A in *. lia.
            - destruct Hs as (b & kk & Hb & Hr). pose proof (KOLD b kk Hb). lia.
            - destruct Hs as (f & kf & Hf & Hr).
              pose proof (af_frames_range RT AF S1 mk f kf ART1 ltac:(rewrite FRS1; right; exact Hf)) as (_ & _ & _ & FLV').
              pose proof (FLV' kel 24 KIN). lia.
            - destruct Hs as (f & kf & Hf & Hr).
              pose proof (af_fshadow_apart RT AF S1 mk f kf ART1 ltac:(rewrite FRS1; right; exact Hf)) as (FS' & _).
              pose proof (FS' kel 24 KIN). lia. }
          idtac "F15-KPF".
          cps_stop.
          art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac|
                                split; [intros zz Hzz; right; right; left; exists kel, 24; split; [solve [eassumption | rewrite LVS; apply in_or_app; right; left; reflexivity]| lia]| exact I]]]]).
          idtac "F15-ART".
          lazymatch goal with MUx : munch _ ?mm _ |- _ =>
            agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; pose proof (KPF _ Hx) as N3; unfold shad, SHB in *;
                                              repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
          idtac "F15-AGF".
          to_entry.
          idtac "F15-ENTRY".
    (* [comment removed for export] *)

          pose proof (kfp_loop_ok_16 RT AF RC GP GPX (kernelSetElement_obj_ok RT AF KSE) Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m pix v cv fr
                       (kfp_exit_ok_16 RT AF RC GP Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m pix v cv fr)) as LOOP.
          eapply cps_conseq; [exact (LOOP 0 ltac:(nia))| | intros c Hc; exact Hc].
          intros c Hc. unfold kfp_head_16. do 34 eexists. split; [exact Hc|].
          idtac "F16-HC".
          split; [lia|]. split; [lia|]. split; [lia|].
          split.
          { split; [| split; [exact D8| split; [exact HOK| split; [lia| split; [lia| split; [exact WH| split; [exact LVB| exact CRB]]]]]]].
            assert (LO0 : 0 <= lo) by lia.
            exact (conj FDO (conj MST (conj ART0 (conj POBJ (conj LOW (conj LOR (conj LO0 (conj SPT (conj SPA (conj SPB
                     (conj LVP (conj FRB (conj DNZ (conj FR0 (conj FR64 NFA))))))))))))))). }
          idtac "F16-LCTX".
    (* [comment removed for export] *)
          split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
          idtac "F17-A".
          split; [unfold kfp_stack_16; exact FR|].
          split; [unfold kfp_frame_lo; exact FRC2|].
          split; [exact FVAL|]. split; [exact FHI|].
          split; [unfold kfp_fshadow; exact FSH|].
          idtac "F17-B".
          split; [eassumption|]. split; [eassumption|]. split; [exact AGF|]. split; [exact POBJ5|].
          split; [exact KOBJ5|].
          idtac "F17-C".
          split; [rewrite LV1; repeat match goal with H : rt_live RT ?X = rt_live RT ?Y |- context [rt_live RT ?X] => rewrite H end; reflexivity|].
          split; [exact FRS1|].
          split; [repeat match goal with H : rt_sp0 RT ?X = rt_sp0 RT ?Y |- context [rt_sp0 RT ?X] => rewrite H end; reflexivity|].
          lia.
    (* [comment removed for export] *)
        }
        { (* [comment removed for export] *)
          brT.
          awalk [e_stack_malloc 1%nat; e_returnErrorPtr; e_lept_stderr; e_kernelCreate; e_pixGetPixel; e_kernelSetElement; 0x919f8; 0x918a8].
          idtac "F18-LEAF".
    (* [comment removed for export] *)
          (* [comment removed for export] *)
          lazymatch goal with MUx : munch ((usp - 256, usp) :: _) ?ma ?mb |- _ =>
            lazymatch goal with A : ART RT ?S ma |- _ =>
              assert (KL3 : keeps_live (rt_live RT S) ma mb)
                by (apply (keeps_live_walk1 RT AF S ma mb fr usp (usp - 256) A
                             ltac:(repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; left; reflexivity)
                             ltac:(repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; unfold STACK_WIN; lia) MUx)) end;
            assert (POBJ3 : pix_obj (rt_live RT Σ) mb pix v cv)
              by (apply (pix_obj_keep _ ma mb pix v cv); [| exact POBJ2];
                  intros bb kk Hin; apply KL3; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact Hin) end.
          clear POBJ2.
          at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                        ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                              repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
          pose proof RERR as RE. unfold returnError_cps in RE.
          eapply cps_seq; [eapply RE with (lo := lo); rt_side idtac; [lit_in | lit_in | lenv_tac | lres_tac..] |].
          idtac "F19-CALL".
          after_call RT AF.
          lazymatch goal with AGx : agree_on _ ?ma ?mb |- cps _ (ASTA RT _ _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
            assert (POBJ4 : pix_obj (rt_live RT Σ) mb pix v cv)
              by (apply (pix_obj_keep _ ma mb pix v cv); [| exact POBJ3];
                  intros bb kk Hin a Ha; apply AGx;
                  right; right; left; exists bb, kk; split; [repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact Hin| exact Ha]) end.
          clear POBJ3.
          fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]).
          idtac "F19-AFTER".
    (* [comment removed for export] *)
          refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
          walk_to AF MST [(usp - 256, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)]
                       [e_stack_malloc 1%nat; e_returnErrorPtr; e_lept_stderr; e_kernelCreate; e_pixGetPixel; e_kernelSetElement; 0x919f8; 0x918a8].
          lazymatch goal with MUx : munch ((usp - 256, usp) :: _) ?ma ?mb |- _ =>
            lazymatch goal with A : ART RT ?S ma |- _ =>
              assert (KL6 : keeps_live (rt_live RT S) ma mb)
                by (apply (keeps_live_walk1 RT AF S ma mb fr usp (usp - 256) A
                             ltac:(repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; left; reflexivity)
                             ltac:(repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; unfold STACK_WIN; lia) MUx)) end;
            assert (POBJ5 : pix_obj (rt_live RT Σ) mb pix v cv)
              by (apply (pix_obj_keep _ ma mb pix v cv); [| exact POBJ4];
                  intros bb kk Hin; apply KL6; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact Hin) end.
          clear POBJ4.
          cps_stop.
          art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
          lazymatch goal with MUx : munch _ ?mm _ |- _ =>
            agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                              repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
          to_entry.
          idtac "F20-EXITSTATE".
    (* [comment removed for export] *)
          pose proof (kfp_exit_ok_16 RT AF RC GP Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m pix v cv fr) as EXITs.
          assert (CTXk : kfp_ctx RT Σ PMc usp lo m pix v cv fr).
          { assert (LO0 : 0 <= lo) by lia.
            exact (conj FDO (conj MST (conj ART0 (conj POBJ (conj LOW (conj LOR (conj LO0 (conj SPT (conj SPA (conj SPB
                     (conj LVP (conj FRB (conj DNZ (conj FR0 (conj FR64 NFA))))))))))))))). }
          lazymatch goal with |- cps _ (ASTA RT ?S _ (eq (entry_st ?a1 _ _ _ ?a5 ?a6 ?a7 _ _ ?a10 ?a11 ?a12 ?a13 ?a14 ?a15 ?a16 ?a17 _ ?a19 _ ?a21 ?a22 ?a23 ?a24 ?a25 _ _ ?a28 ?a29 ?a30 ?a31 ?FF ?fcc _ ?mm))) _ =>
            eapply (cps_conseq _ _ _ _ _ (EXITs S mm 0 (Z_to_bv 64 1102416563)
                                  _ _ _
                                  a1 a5 a6 a7 a10 a11 a12 a13 a14 a15 a16 a17 a19 a21 a22 a23 a24 a25 a28 a29 a30 a31 FF fcc CTXk
                                  ltac:(eassumption) ltac:(eassumption) ltac:(eassumption) ltac:(eassumption)
                                  ltac:(unfold kfp_stack_16; exact FR)
                                  ltac:(lazymatch goal with H : rw_cells _ _ fr (C8 _ :: _) |- _ => exact (rw_cells_head _ _ _ _ H) end)
                                  ltac:(unfold kfp_fshadow; exact FSH)
                                  ltac:(eassumption) ltac:(eassumption) AGF _ _ _ _ _))
          end.
          Unshelve.
    (* [comment removed for export] *)
          1: (intros c Hc; exact Hc).
          1: (intros c Hc; exact Hc).
          1: (repeat match goal with H : rt_frames RT ?X = rt_frames RT ?Y |- context [rt_frames RT ?X] => rewrite H end; first [exact FRS | reflexivity]).
          1: (repeat match goal with H : rt_sp0 RT ?X = rt_sp0 RT ?Y |- context [rt_sp0 RT ?X] => rewrite H end; reflexivity).
          1: (repeat match goal with H : rt_credit RT ?X = _ |- context [rt_credit RT ?X] => rewrite H end; lia).
          1: (apply (km_pix_obj_mono (rt_live RT Σ)); [| exact POBJ5]; intros e He;
              repeat match goal with H : rt_live RT ?X = rt_live RT ?Y |- context [rt_live RT ?X] => rewrite H end; exact He).
          1: (left; split; [reflexivity|]; repeat match goal with H : rt_live RT ?X = rt_live RT ?Y |- context [rt_live RT ?X] => rewrite H end; reflexivity).
    (* [comment removed for export] *)
        }
      }
      { (* [comment removed for export] *)
        brT.
        awalk [e_stack_malloc 1%nat; e_returnErrorPtr; e_lept_stderr; e_kernelCreate; e_pixGetPixel; e_kernelSetElement; 0x919f8; 0x918a8].
        idtac "F23-LEAF".
    (* [comment removed for export] *)
          (* [comment removed for export] *)
          lazymatch goal with MUx : munch ((usp - 256, usp) :: _) ?ma ?mb |- _ =>
            lazymatch goal with A : ART RT ?S ma |- _ =>
              assert (KL3 : keeps_live (rt_live RT S) ma mb)
                by (apply (keeps_live_walk1 RT AF S ma mb fr usp (usp - 256) A
                             ltac:(repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; left; reflexivity)
                             ltac:(repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; unfold STACK_WIN; lia) MUx)) end;
            assert (POBJ3 : pix_obj (rt_live RT Σ) mb pix v cv)
              by (apply (pix_obj_keep _ ma mb pix v cv); [| exact POBJ2];
                  intros bb kk Hin; apply KL3; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact Hin) end.
          clear POBJ2.
          at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                        ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                              repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
          pose proof RERR as RE. unfold returnError_cps in RE.
          eapply cps_seq; [eapply RE with (lo := lo); rt_side idtac; [lit_in | lit_in | lenv_tac | lres_tac..] |].
          idtac "F19-CALL".
          after_call RT AF.
          lazymatch goal with AGx : agree_on _ ?ma ?mb |- cps _ (ASTA RT _ _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
            assert (POBJ4 : pix_obj (rt_live RT Σ) mb pix v cv)
              by (apply (pix_obj_keep _ ma mb pix v cv); [| exact POBJ3];
                  intros bb kk Hin a Ha; apply AGx;
                  right; right; left; exists bb, kk; split; [repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact Hin| exact Ha]) end.
          clear POBJ3.
          fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]).
          idtac "F19-AFTER".
    (* [comment removed for export] *)
          refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
          walk_to AF MST [(usp - 256, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)]
                       [e_stack_malloc 1%nat; e_returnErrorPtr; e_lept_stderr; e_kernelCreate; e_pixGetPixel; e_kernelSetElement; 0x919f8; 0x918a8].
          lazymatch goal with MUx : munch ((usp - 256, usp) :: _) ?ma ?mb |- _ =>
            lazymatch goal with A : ART RT ?S ma |- _ =>
              assert (KL6 : keeps_live (rt_live RT S) ma mb)
                by (apply (keeps_live_walk1 RT AF S ma mb fr usp (usp - 256) A
                             ltac:(repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; left; reflexivity)
                             ltac:(repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; unfold STACK_WIN; lia) MUx)) end;
            assert (POBJ5 : pix_obj (rt_live RT Σ) mb pix v cv)
              by (apply (pix_obj_keep _ ma mb pix v cv); [| exact POBJ4];
                  intros bb kk Hin; apply KL6; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact Hin) end.
          clear POBJ4.
          cps_stop.
          art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
          lazymatch goal with MUx : munch _ ?mm _ |- _ =>
            agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                              repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
          to_entry.
          idtac "F20-EXITSTATE".
    (* [comment removed for export] *)
          pose proof (kfp_exit_ok_16 RT AF RC GP Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m pix v cv fr) as EXITs.
          assert (CTXk : kfp_ctx RT Σ PMc usp lo m pix v cv fr).
          { assert (LO0 : 0 <= lo) by lia.
            exact (conj FDO (conj MST (conj ART0 (conj POBJ (conj LOW (conj LOR (conj LO0 (conj SPT (conj SPA (conj SPB
                     (conj LVP (conj FRB (conj DNZ (conj FR0 (conj FR64 NFA))))))))))))))). }
          lazymatch goal with |- cps _ (ASTA RT ?S _ (eq (entry_st ?a1 _ _ _ ?a5 ?a6 ?a7 _ _ ?a10 ?a11 ?a12 ?a13 ?a14 ?a15 ?a16 ?a17 _ ?a19 _ ?a21 ?a22 ?a23 ?a24 ?a25 _ _ ?a28 ?a29 ?a30 ?a31 ?FF ?fcc _ ?mm))) _ =>
            eapply (cps_conseq _ _ _ _ _ (EXITs S mm 0 (Z_to_bv 64 1102416563)
                                  _ _ _
                                  a1 a5 a6 a7 a10 a11 a12 a13 a14 a15 a16 a17 a19 a21 a22 a23 a24 a25 a28 a29 a30 a31 FF fcc CTXk
                                  ltac:(eassumption) ltac:(eassumption) ltac:(eassumption) ltac:(eassumption)
                                  ltac:(unfold kfp_stack_16; exact FR)
                                  ltac:(lazymatch goal with H : rw_cells _ _ fr (C8 _ :: _) |- _ => exact (rw_cells_head _ _ _ _ H) end)
                                  ltac:(unfold kfp_fshadow; exact FSH)
                                  ltac:(eassumption) ltac:(eassumption) AGF _ _ _ _ _))
          end.
          Unshelve.
    (* [comment removed for export] *)
          1: (intros c Hc; exact Hc).
          1: (intros c Hc; exact Hc).
          1: (repeat match goal with H : rt_frames RT ?X = rt_frames RT ?Y |- context [rt_frames RT ?X] => rewrite H end; first [exact FRS | reflexivity]).
          1: (repeat match goal with H : rt_sp0 RT ?X = rt_sp0 RT ?Y |- context [rt_sp0 RT ?X] => rewrite H end; reflexivity).
          1: (repeat match goal with H : rt_credit RT ?X = _ |- context [rt_credit RT ?X] => rewrite H end; lia).
          1: (apply (km_pix_obj_mono (rt_live RT Σ)); [| exact POBJ5]; intros e He;
              repeat match goal with H : rt_live RT ?X = rt_live RT ?Y |- context [rt_live RT ?X] => rewrite H end; exact He).
          1: (left; split; [reflexivity|]; repeat match goal with H : rt_live RT ?X = rt_live RT ?Y |- context [rt_live RT ?X] => rewrite H end; reflexivity).
    (* [comment removed for export] *)
      }
    }
    { (* [comment removed for export] *)
      brT.
      awalk [e_stack_malloc 1%nat; e_returnErrorPtr; e_lept_stderr; e_kernelCreate; e_pixGetPixel; e_kernelSetElement; 0x919f8; 0x918a8].
      idtac "F24-LEAF".
    (* [comment removed for export] *)
          (* [comment removed for export] *)
          lazymatch goal with MUx : munch ((usp - 256, usp) :: _) ?ma ?mb |- _ =>
            lazymatch goal with A : ART RT ?S ma |- _ =>
              assert (KL3 : keeps_live (rt_live RT S) ma mb)
                by (apply (keeps_live_walk1 RT AF S ma mb fr usp (usp - 256) A
                             ltac:(repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; left; reflexivity)
                             ltac:(repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; unfold STACK_WIN; lia) MUx)) end;
            assert (POBJ3 : pix_obj (rt_live RT Σ) mb pix v cv)
              by (apply (pix_obj_keep _ ma mb pix v cv); [| exact POBJ2];
                  intros bb kk Hin; apply KL3; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact Hin) end.
          clear POBJ2.
          at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                        ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                              repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
          pose proof RERR as RE. unfold returnError_cps in RE.
          eapply cps_seq; [eapply RE with (lo := lo); rt_side idtac; [lit_in | lit_in | lenv_tac | lres_tac..] |].
          idtac "F19-CALL".
          after_call RT AF.
          lazymatch goal with AGx : agree_on _ ?ma ?mb |- cps _ (ASTA RT _ _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
            assert (POBJ4 : pix_obj (rt_live RT Σ) mb pix v cv)
              by (apply (pix_obj_keep _ ma mb pix v cv); [| exact POBJ3];
                  intros bb kk Hin a Ha; apply AGx;
                  right; right; left; exists bb, kk; split; [repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact Hin| exact Ha]) end.
          clear POBJ3.
          fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]).
          idtac "F19-AFTER".
    (* [comment removed for export] *)
          refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
          walk_to AF MST [(usp - 256, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)]
                       [e_stack_malloc 1%nat; e_returnErrorPtr; e_lept_stderr; e_kernelCreate; e_pixGetPixel; e_kernelSetElement; 0x919f8; 0x918a8].
          lazymatch goal with MUx : munch ((usp - 256, usp) :: _) ?ma ?mb |- _ =>
            lazymatch goal with A : ART RT ?S ma |- _ =>
              assert (KL6 : keeps_live (rt_live RT S) ma mb)
                by (apply (keeps_live_walk1 RT AF S ma mb fr usp (usp - 256) A
                             ltac:(repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; left; reflexivity)
                             ltac:(repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; unfold STACK_WIN; lia) MUx)) end;
            assert (POBJ5 : pix_obj (rt_live RT Σ) mb pix v cv)
              by (apply (pix_obj_keep _ ma mb pix v cv); [| exact POBJ4];
                  intros bb kk Hin; apply KL6; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact Hin) end.
          clear POBJ4.
          cps_stop.
          art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
          lazymatch goal with MUx : munch _ ?mm _ |- _ =>
            agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                              repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
          to_entry.
          idtac "F20-EXITSTATE".
    (* [comment removed for export] *)
          pose proof (kfp_exit_ok_16 RT AF RC GP Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m pix v cv fr) as EXITs.
          assert (CTXk : kfp_ctx RT Σ PMc usp lo m pix v cv fr).
          { assert (LO0 : 0 <= lo) by lia.
            exact (conj FDO (conj MST (conj ART0 (conj POBJ (conj LOW (conj LOR (conj LO0 (conj SPT (conj SPA (conj SPB
                     (conj LVP (conj FRB (conj DNZ (conj FR0 (conj FR64 NFA))))))))))))))). }
          lazymatch goal with |- cps _ (ASTA RT ?S _ (eq (entry_st ?a1 _ _ _ ?a5 ?a6 ?a7 _ _ ?a10 ?a11 ?a12 ?a13 ?a14 ?a15 ?a16 ?a17 _ ?a19 _ ?a21 ?a22 ?a23 ?a24 ?a25 _ _ ?a28 ?a29 ?a30 ?a31 ?FF ?fcc _ ?mm))) _ =>
            eapply (cps_conseq _ _ _ _ _ (EXITs S mm 0 (Z_to_bv 64 1102416563)
                                  _ _ _
                                  a1 a5 a6 a7 a10 a11 a12 a13 a14 a15 a16 a17 a19 a21 a22 a23 a24 a25 a28 a29 a30 a31 FF fcc CTXk
                                  ltac:(eassumption) ltac:(eassumption) ltac:(eassumption) ltac:(eassumption)
                                  ltac:(unfold kfp_stack_16; exact FR)
                                  ltac:(lazymatch goal with H : rw_cells _ _ fr (C8 _ :: _) |- _ => exact (rw_cells_head _ _ _ _ H) end)
                                  ltac:(unfold kfp_fshadow; exact FSH)
                                  ltac:(eassumption) ltac:(eassumption) AGF _ _ _ _ _))
          end.
          Unshelve.
    (* [comment removed for export] *)
          1: (intros c Hc; exact Hc).
          1: (intros c Hc; exact Hc).
          1: (repeat match goal with H : rt_frames RT ?X = rt_frames RT ?Y |- context [rt_frames RT ?X] => rewrite H end; first [exact FRS | reflexivity]).
          1: (repeat match goal with H : rt_sp0 RT ?X = rt_sp0 RT ?Y |- context [rt_sp0 RT ?X] => rewrite H end; reflexivity).
          1: (repeat match goal with H : rt_credit RT ?X = _ |- context [rt_credit RT ?X] => rewrite H end; lia).
          1: (apply (km_pix_obj_mono (rt_live RT Σ)); [| exact POBJ5]; intros e He;
              repeat match goal with H : rt_live RT ?X = rt_live RT ?Y |- context [rt_live RT ?X] => rewrite H end; exact He).
          1: (left; split; [reflexivity|]; repeat match goal with H : rt_live RT ?X = rt_live RT ?Y |- context [rt_live RT ?X] => rewrite H end; reflexivity).
    (* [comment removed for export] *)
    }
Qed.
End FROMPIX.
