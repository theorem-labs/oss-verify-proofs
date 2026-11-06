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
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.B17 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit Lept_chain Lept_leaf Lept_objkit Lept_deserkit Km_setelem Km_iface Km_walkkit Km_kit Km_setelem_obj Km_frompix_defs.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.B17 Require Import LeptB_guard LeptB_guard2 LeptB_guard3.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section KFP_LOOP.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis GPX : pixGetPixel_cps RT.
Hypothesis KSEO : kernelSetElement_obj_cps RT.
Variables (Σ : rts RT) (PMc : Model -> Prop) (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (usp lo : Z) (m : mem)
          (pix : Z) (v : pixv) (cv : cmapv) (fr : Z).

Lemma kfp_step_ok_0 : kfp_exit_stmt_0 RT Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m pix v cv fr ->
  forall k, 0 <= k < p_w v * p_h v ->
  cps asegs (kfp_head_0 RT Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m pix v cv fr k)
    (fun c => (k + 1 < p_w v * p_h v /\ kfp_head_0 RT Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m pix v cv fr (k + 1) c)
              \/ (k + 1 = p_w v * p_h v /\ kfp_post RT Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m pix v cv c)).
Proof using AF RC GP GPX KSEO.
  intros EXIT k Hk. unfold kfp_head_0 at 1.
  apply cps_ex_l; intros S0.
  apply cps_ex_l; intros m0.
  apply cps_ex_l; intros i.
  apply cps_ex_l; intros j.
  apply cps_ex_l; intros kel.
  apply cps_ex_l; intros data.
  apply cps_ex_l; intros rows.
  apply cps_ex_l; intros x0.
  apply cps_ex_l; intros f0.
  apply cps_ex_l; intros f1.
  apply cps_ex_l; intros f2.
  apply cps_ex_l; intros f3.
  apply cps_ex_l; intros f4.
  apply cps_ex_l; intros js.
  apply cps_ex_l; intros j0.
  apply cps_ex_l; intros r1.
  apply cps_ex_l; intros r5.
  apply cps_ex_l; intros r6.
  apply cps_ex_l; intros r7.
  apply cps_ex_l; intros r10.
  apply cps_ex_l; intros r11.
  apply cps_ex_l; intros r12.
  apply cps_ex_l; intros r13.
  apply cps_ex_l; intros r14.
  apply cps_ex_l; intros r15.
  apply cps_ex_l; intros r16.
  apply cps_ex_l; intros r17.
  apply cps_ex_l; intros r28.
  apply cps_ex_l; intros r29.
  apply cps_ex_l; intros r30.
  apply cps_ex_l; intros r31.
  apply cps_ex_l; intros F'.
  apply cps_ex_l; intros fc'.
  apply cps_and_pure_r; intros (KE & IB & JB & LCTX & ART1 & MI1 & WM1 & ST1 & FR & FLO & PVC & FHI & FSH & LH & SSP & AGF & POBJ & KOBJ & LV & FRS & SP0S & CRS).
  destruct LCTX as (CTX & D8 & HOK & H3 & W3 & WH & LVB & CRB).
  pose proof CTX as (FDO & MST & ART0 & POBJ0 & LOW & LOR & LO0 & SPT & SPA & SPB & LVP & FRB & DNZ & FR0 & FR64 & NFA).
  unfold kfp_stack_0 in FR. unfold kfp_frame_lo in FLO. unfold kfp_fshadow in FSH.
  destruct (af_client_consts RT AF S0 m0 ART1) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF S0 m0 ART1) as SP0R. pose proof (af_sp0_win RT AF S0 m0 ART1) as SP0W.
  rewrite SP0S in SP0R, SP0W.
  unfold entry_st, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  set (PF := kfp_PF RT Σ usp) in *.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a Ha. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [HH|HH]; [left; exact HH| right; unfold STACK_WIN in HH; lia]. }
  pose proof ST1 as (STa & STb & _).
  pose proof (af_frames_range RT AF S0 m0 fr 1%nat ART1 ltac:(rewrite FRS; left; reflexivity)) as (FRA0 & FRHI & _ & _).
  pose proof (af_frames_align RT AF S0 m0 fr 1%nat ART1 ltac:(rewrite FRS; left; reflexivity)) as (FRA64 & FRSEG).
  pose proof (af_frames_hi RT AF S0 m0 fr 1%nat ART1 ltac:(rewrite FRS; left; reflexivity)) as FRSH.
  change (fs_size 1) with 128 in FRHI, FRSH. rewrite SP0S in FRHI. unfold STACK_WIN, SEGTOP_A in FRHI, FRSEG.
  (* [comment removed for export] *)
  park_disj.
  walk_to AF MST [(usp - 128, usp)] [e_stack_malloc 1%nat; e_returnErrorPtr; e_lept_stderr; e_kernelCreate; e_pixGetPixel; e_kernelSetElement; 0x923b8].
  idtac "L1-WALK".
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  pose proof FSH as SV. split_at SV 10%nat SV2. split_at SV2 1%nat SV3. clear SV SV3.
  idtac "L2-SV".
  (* [comment removed for export] *)
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
  idtac "L3-ATCALL".
  pose proof GPX as GX. unfold pixGetPixel_cps in GX.
  eapply cps_seq.
  { eapply GX with (lo := lo) (pix := pix) (v := v) (cv := cv) (x := j) (y := i) (pv := fr + 80) (x0 := x0); rt_side idtac.
    1: (apply (km_pix_obj_mono (rt_live RT Σ)); [intros e He; rewrite LV; apply km_live_in_old; exact He| exact POBJ]).
    1: (unfold optrF, own_frame; split;
        [ exists fr, 1%nat; split; [rewrite FRS; left; reflexivity|];
          change (fs_size 1) with 128;
          split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
          split; [lia|]; split; [lia|];
          replace (shad (fr + 80)) with (fr / 8 + 2147450890) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
          destruct SV2 as [[_ B] _]; exact B
        | unfold SEGTOP_A; unfold parked in FRSH; clear - FRA0 FR64 FRSH FRSEG; repeat split; first [lia | Z.div_mod_to_equations; lia] ]).
    1: lenv_tac.
    1: (pose proof (km_cost_bound (p_h v) (p_w v) H3 W3 WH) as KCB;
        pose proof KOBJ as (_ & _ & _ & _ & LEN & _);
        unfold lres; rewrite FRS, LV; unfold km_live; rewrite length_app, length_rev, length_map; cbn [length];
        split; [lia| split; [lia| split; [lia| ]]];
        intros p n Hin; apply in_app_or in Hin as [Hin|[Hin|[Hin|Hin]]];
        [ apply in_rev in Hin; apply in_map_iff in Hin as (r & Er & _); injection Er as _ <-; lia
        | injection Hin as _ <-; lia | injection Hin as _ <-; lia | exact (LVP p n Hin) ]). }
  idtac "L3-CALL".
  after_call RT AF.
  idtac "L4-AFTER".
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  pose proof (af_frames_range RT AF S0 m0 fr 1%nat ART1 ltac:(rewrite FRS; left; reflexivity)) as (_ & _ & _ & FLV).
  change (fs_size 1) with 128 in FLV.
  lazymatch goal with AGx : agree_on _ m0 ?m1 |- _ =>
    assert (KLp : keeps_live (rt_live RT S0) m0 m1)
      by (intros bb kk Hin a Ha; apply AGx; split;
          [ right; right; left; exists bb, kk; split; [repeat match goal with H : rt_live _ _ = rt_live RT S0 |- _ => rewrite H end; exact Hin| exact Ha]
          | cbn [outside]; split; [| exact I]; pose proof (FLV bb kk Hin); lia ]);
    pose proof (kel_obj_keep _ m0 m1 kel (p_h v) (p_w v) 2 2 data rows KLp KOBJ) as KOBJ1;
    assert (POBJ1 : pix_obj (rt_live RT Σ) m1 pix v cv)
      by (apply (pix_obj_keep _ m0 m1 pix v cv); [| exact POBJ];
          intros bb kk Hin; apply KLp; rewrite LV; apply km_live_in_old; exact Hin) end.
  clear KOBJ POBJ.
  idtac "L4C-OBJ".
  fold_ag ltac:(fun Hx => split;
    [ apply (aclient_mono _ _ usp _ _ _ _ Hx);
      [ intros e He; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; apply km_live_in_old; exact He
      | solve [frames_sub_tac] | lia ]
    | cbn [outside]; destruct (NFA _ Hx) as [N1 N2]; split; [lia| exact I] ]).
  idtac "L4-FOLD".
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  pose proof KOBJ1 as (_ & _ & _ & _ & LEN & _).
  destruct (nth_error rows (Z.to_nat i)) as [r|] eqn:NR; [| apply nth_error_None in NR; lia].
  pose proof (nth_error_In _ _ NR) as RIN.
  assert (RLV : In (r, 4 * p_w v) (rt_live RT S0)) by (rewrite LV; apply km_live_in_row; exact RIN).
  pose proof (FLV r (4 * p_w v) RLV) as RFR.
  pose proof (af_fshadow_apart RT AF S0 m0 fr 1%nat ART1 ltac:(rewrite FRS; left; reflexivity)) as (RFS & _).
  specialize (RFS r (4 * p_w v) RLV). change (fs_size 1) with 128 in RFS. unfold shad, SHB in RFS.
  pose proof (af_live_range RT AF S0 m0 r (4 * p_w v) ART1 RLV) as (_ & RR1 & RR2).
  pose proof (gp_live_hi RT GP S0 m0 r (4 * p_w v) ART1 RLV) as RR3.
  unfold STACK_WIN, SEGTOP_A in RR1, RR2. rewrite SP0S in RR1.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  idtac "L5-FACTS".
  walk_to AF MST [(usp - 128, usp)] [e_stack_malloc 1%nat; e_returnErrorPtr; e_lept_stderr; e_kernelCreate; e_pixGetPixel; e_kernelSetElement; 0x923b8].
  idtac "L5-WALK".
  (* [comment removed for export] *)
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
  idtac "L6-ATCALL".
  pose proof KSEO as KS. unfold kernelSetElement_obj_cps in KS.
  eapply cps_seq.
  { eapply KS with (lo := lo) (kel := kel) (sy := p_h v) (sx := p_w v) (cy := 2) (cx := 2) (data := data) (rows := rows) (i := i) (j := j) (r := r);
      rt_side idtac.
    all: lazymatch goal with
         | |- kel_obj _ _ _ _ _ _ _ _ _ =>
             first [ exact KOBJ1 | match goal with H : rt_live RT ?X = rt_live RT ?Y |- kel_obj (rt_live RT ?X) _ _ _ _ _ _ _ _ => rewrite H; exact KOBJ1 end ]
         | |- nth_error _ _ = _ => exact NR
         | |- lenv _ _ _ _ _ _ => lenv_tac
         | |- ?g => idtac "LEFT-KS:" g
         end. }
  idtac "L6-CALL".
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  assert (ROLD : forall b kk, In (b, kk) (rt_live RT Σ) -> r + 4 * p_w v <= b \/ b + kk <= r).
  { intros b kk Hb.
    assert (Hr : In (r, 4 * p_w v) (rev (map (fun r0 => (r0, 4 * p_w v)) rows)))
      by (apply in_rev; rewrite rev_involutive; apply in_map_iff; exists r; split; [reflexivity| exact RIN]).
    destruct (in_split _ _ Hr) as (l1 & l2 & E).
    apply (af_live_disj RT AF S0 m0 r (4 * p_w v) b kk l1 (l2 ++ (data, 8 * p_h v) :: (kel, 24) :: rt_live RT Σ) ART1).
    - rewrite LV. unfold km_live. rewrite E. rewrite <- app_assoc. reflexivity.
    - apply in_or_app. right. apply in_or_app. right. right. right. exact Hb. }
  idtac "L7-ROLD".
  try (unfold parked in RFR). try (unfold parked in RFS).
  after_call RT AF.
  idtac "L7-AFTER".
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with AGx : agree_on _ ?m1 ?m2, KO : kel_obj _ ?m2 kel _ _ _ _ _ _ |- _ =>
    assert (POBJ2 : pix_obj (rt_live RT Σ) m2 pix v cv)
      by (apply (pix_obj_keep _ m1 m2 pix v cv); [| exact POBJ1];
          intros bb kk Hin a Ha; apply AGx; split;
          [ right; right; left; exists bb, kk; split;
            [ repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; apply km_live_in_old; exact Hin
            | exact Ha ]
          | cbn [outside]; split; [| exact I]; pose proof (ROLD bb kk Hin); lia ]);
    rename KO into KOBJ2 end.
  clear POBJ1 KOBJ1.
  idtac "L8-OBJ".
  (* [comment removed for export] *)
  assert (RPF : forall z, PF z -> z < r \/ r + 4 * p_w v <= z).
  { intros z Hz. unfold PF, kfp_PF, aclient in Hz. unfold USTACK_TOP in Hz.
    destruct Hz as [Hs|[Hs|[Hs|[Hs|Hs]]]].
    - lia.
    - pose proof (client_static_below _ Hs). pose proof (client_static_ge _ Hs). unfold SEGTOP_A in *. unfold parked in RR2. lia.
    - destruct Hs as (b & kk & Hb & Hr). pose proof (ROLD b kk Hb). lia.
    - destruct Hs as (f & kf & Hf & Hr).
      pose proof (af_frames_range RT AF S0 m0 f kf ART1 ltac:(rewrite FRS; right; exact Hf)) as (_ & _ & _ & FLV').
      pose proof (FLV' r (4 * p_w v) RLV). lia.
    - destruct Hs as (f & kf & Hf & Hr).
      pose proof (af_fshadow_apart RT AF S0 m0 f kf ART1 ltac:(rewrite FRS; right; exact Hf)) as (FS' & _).
      pose proof (FS' r (4 * p_w v) RLV). lia. }
  idtac "L8-RPF".
  fold_ag ltac:(fun Hx => split;
    [ apply (aclient_mono _ _ usp _ _ _ _ Hx);
      [ intros e He; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; apply km_live_in_old; exact He
      | solve [frames_sub_tac] | lia ]
    | cbn [outside]; split; [| exact I]; pose proof (RPF _ Hx); lia ]).
  idtac "L8-FOLD".
  (* [comment removed for export] *)
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  walk_to AF MST [(usp - 128, usp)] [e_stack_malloc 1%nat; e_returnErrorPtr; e_lept_stderr; e_kernelCreate; e_pixGetPixel; e_kernelSetElement; 0x92508; 0x923b8; 0x924f0].
  idtac "L9-WALK".
  (* [comment removed for export] *)
  rewrite ?(bv_swrap_small 32 (j + 1)) by (change (bv_half_modulus 32) with (2^31); lia).
  rewrite ?(sx32_small (p_w v)) by lia.
  destruct (Z_lt_le_dec (j + 1) (p_w v)) as [JN|JE].
  { (* [comment removed for export] *)
    try brT.
    idtac "L10-A".
  (* [comment removed for export] *)
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I]).
    lazymatch goal with MUx : munch _ ?mm _ |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]) end.
    idtac "L11-ART".
    to_entry.
    assert (KN : k + 1 < p_w v * p_h v) by (rewrite KE; nia).
    apply cps_finish; intros c Hc. left. split; [exact KN|].
    unfold kfp_head_0. do 33 eexists. split; [exact Hc|].
    idtac "L11-HC".
  (* [comment removed for export] *)
    split; [lia|]. split; [lia|]. split; [lia|].
    split; [exact (conj CTX (conj D8 (conj HOK (conj H3 (conj W3 (conj WH (conj LVB CRB)))))))|].
    idtac "L12-A".
    split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    idtac "L12-B".
    split; [unfold kfp_stack_0; exact FR|].
    split; [unfold kfp_frame_lo; exact FLO|].
    split; [eassumption|]. split; [eassumption|].
    split; [unfold kfp_fshadow; exact FSH|].
    idtac "L12-C".
    split; [eassumption|]. split; [eassumption|]. split; [exact AGF|]. split; [exact POBJ2|].
    idtac "L12-D".
    lazymatch goal with |- ?g => idtac "G:" g end.
  (* [comment removed for export] *)
    split; [lazymatch goal with |- kel_obj (rt_live RT ?A) _ _ _ _ _ _ _ _ => match goal with H : rt_live RT A = _ |- _ => rewrite H end end; exact KOBJ2|].
    idtac "L13-KOBJ".
    repeat match goal with H : rt_live RT ?X = rt_live RT ?Y |- context [rt_live RT ?X] => rewrite H end.
    repeat match goal with H : rt_frames RT ?X = rt_frames RT ?Y |- context [rt_frames RT ?X] => rewrite H end.
    repeat match goal with H : rt_sp0 RT ?X = rt_sp0 RT ?Y |- context [rt_sp0 RT ?X] => rewrite H end.
    split; [first [exact LV | reflexivity]|]. split; [first [exact FRS | reflexivity]|]. split; [first [exact SP0S | reflexivity]|].
    idtac "L13-EQ".
    lazymatch goal with |- ?g => idtac "G:" g end.
  (* [comment removed for export] *)
    repeat match goal with H : rt_credit RT ?X = _ |- context [rt_credit RT ?X] => rewrite H end. lia.
  }
  idtac "L14-A-DONE".
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  try brF.
  awalk [e_stack_malloc 1%nat; e_returnErrorPtr; e_lept_stderr; e_kernelCreate; e_pixGetPixel; e_kernelSetElement; 0x92508; 0x923b8].
  idtac "L15-WALK".
  (* [comment removed for export] *)
  rewrite ?(bv_swrap_small 32 (i + 1)) by (change (bv_half_modulus 32) with (2^31); lia).
  rewrite ?(sx32_small (p_h v)) by lia.
  assert (JW : j + 1 = p_w v) by lia.
  destruct (Z_lt_le_dec (i + 1) (p_h v)) as [IN|IE].
  { (* [comment removed for export] *)
    try brF.
    awalk [e_stack_malloc 1%nat; e_returnErrorPtr; e_lept_stderr; e_kernelCreate; e_pixGetPixel; e_kernelSetElement; 0x92508; 0x923b8].
    idtac "L16-B1".
  (* [comment removed for export] *)
    rewrite ?(sx32_small (p_w v)) by lia. try brF.
    awalk [e_stack_malloc 1%nat; e_returnErrorPtr; e_lept_stderr; e_kernelCreate; e_pixGetPixel; e_kernelSetElement; 0x92508; 0x923b8].
    idtac "L17-B1".
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I]).
    lazymatch goal with MUx : munch _ ?mm _ |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]) end.
    to_entry.
    assert (KN : k + 1 < p_w v * p_h v) by (rewrite KE; nia).
    apply cps_finish; intros c Hc. left. split; [exact KN|].
    unfold kfp_head_0. do 33 eexists. split; [exact Hc|].
    idtac "L17-HC".
    split; [nia|]. split; [lia|]. split; [lia|].
    split; [exact (conj CTX (conj D8 (conj HOK (conj H3 (conj W3 (conj WH (conj LVB CRB)))))))|].
    split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    split; [unfold kfp_stack_0; exact FR|].
    split; [unfold kfp_frame_lo; exact FLO|].
    split; [eassumption|]. split; [eassumption|].
    split; [unfold kfp_fshadow; exact FSH|].
    split; [eassumption|]. split; [eassumption|]. split; [exact AGF|]. split; [exact POBJ2|].
    split; [lazymatch goal with |- kel_obj (rt_live RT ?A) _ _ _ _ _ _ _ _ => match goal with H : rt_live RT A = _ |- _ => rewrite H end end; exact KOBJ2|].
    repeat match goal with H : rt_live RT ?X = rt_live RT ?Y |- context [rt_live RT ?X] => rewrite H end.
    repeat match goal with H : rt_frames RT ?X = rt_frames RT ?Y |- context [rt_frames RT ?X] => rewrite H end.
    repeat match goal with H : rt_sp0 RT ?X = rt_sp0 RT ?Y |- context [rt_sp0 RT ?X] => rewrite H end.
    split; [first [exact LV | reflexivity]|]. split; [first [exact FRS | reflexivity]|]. split; [first [exact SP0S | reflexivity]|].
    repeat match goal with H : rt_credit RT ?X = _ |- context [rt_credit RT ?X] => rewrite H end. lia.
  }
  idtac "L17-B1-DONE".
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  try brT.
  cps_stop.
  art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I]).
  lazymatch goal with MUx : munch _ ?mm _ |- _ =>
    agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]) end.
  to_entry.
  assert (KX : k + 1 = p_w v * p_h v) by (rewrite KE; nia).
  pose proof (km_cost_bound (p_h v) (p_w v) H3 W3 WH) as KCB.
  idtac "L18-EXITSTATE".
  lazymatch goal with |- cps _ (ASTA RT ?S _ (eq (entry_st ?a1 _ _ _ ?a5 ?a6 ?a7 _ _ ?a10 ?a11 ?a12 ?a13 ?a14 ?a15 ?a16 ?a17 _ ?a19 _ ?a21 ?a22 ?a23 ?a24 ?a25 _ _ ?a28 ?a29 ?a30 ?a31 ?FF ?fcc _ ?mm))) _ =>
    eapply (cps_conseq _ _ _ _ _ (EXIT S mm kel (Z_to_bv 64 1102416563)
                                  js j0
                                  a1 a5 a6 a7 a10 a11 a12 a13 a14 a15 a16 a17 a19 a21 a22 a23 a24 a25 a28 a29 a30 a31 FF fcc CTX
                                  ltac:(eassumption) ltac:(eassumption) ltac:(eassumption) ltac:(eassumption)
                                  ltac:(unfold kfp_stack_0; exact FR) (rw_cells_head _ _ _ _ FLO) ltac:(unfold kfp_fshadow; exact FSH)
                                  ltac:(eassumption) ltac:(eassumption) AGF _ _ _ _ _))
  end.
  idtac "L18-EXIT".
  Unshelve.
  (* [comment removed for export] *)
  1: (intros c Hc; exact Hc).
  1: (intros c Hc; subst QF; cbv beta; right; split; [exact KX| exact Hc]).
  1: (repeat match goal with H : rt_frames RT ?X = rt_frames RT ?Y |- context [rt_frames RT ?X] => rewrite H end; first [exact FRS | reflexivity]).
  1: (repeat match goal with H : rt_sp0 RT ?X = rt_sp0 RT ?Y |- context [rt_sp0 RT ?X] => rewrite H end; first [exact SP0S | reflexivity]).
  1: (repeat match goal with H : rt_credit RT ?X = _ |- context [rt_credit RT ?X] => rewrite H end; lia).
  1: (apply (km_pix_obj_mono (rt_live RT Σ)); [| exact POBJ2]; intros e He;
      repeat match goal with H : rt_live RT ?X = rt_live RT ?Y |- context [rt_live RT ?X] => rewrite H end;
      rewrite LV; apply km_live_in_old; exact He).
  1: (right; exists data, rows; split; [exact D8|]; split;
      [ lazymatch goal with |- kel_obj (rt_live RT ?A) _ _ _ _ _ _ _ _ => match goal with H : rt_live RT A = _ |- _ => rewrite H end end; exact KOBJ2
      | repeat match goal with H : rt_live RT ?X = rt_live RT ?Y |- context [rt_live RT ?X] => rewrite H end; exact LV ]).
Qed.

Lemma kfp_loop_ok_0 : kfp_exit_stmt_0 RT Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m pix v cv fr ->
  forall k, 0 <= k < p_w v * p_h v ->
  cps asegs (kfp_head_0 RT Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m pix v cv fr k)
            (kfp_post RT Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m pix v cv).
Proof using AF RC GP GPX KSEO.
  intros EXIT. apply (cps_loop_Z (kfp_head_0 RT Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m pix v cv fr)
                                (kfp_post RT Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m pix v cv) (p_w v * p_h v)).
  exact (kfp_step_ok_0 EXIT).
Qed.

Lemma kfp_step_ok_16 : kfp_exit_stmt_16 RT Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m pix v cv fr ->
  forall k, 0 <= k < p_w v * p_h v ->
  cps asegs (kfp_head_16 RT Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m pix v cv fr k)
    (fun c => (k + 1 < p_w v * p_h v /\ kfp_head_16 RT Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m pix v cv fr (k + 1) c)
              \/ (k + 1 = p_w v * p_h v /\ kfp_post RT Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m pix v cv c)).
Proof using AF RC GP GPX KSEO.
  intros EXIT k Hk. unfold kfp_head_16 at 1.
  apply cps_ex_l; intros S0.
  apply cps_ex_l; intros m0.
  apply cps_ex_l; intros i.
  apply cps_ex_l; intros j.
  apply cps_ex_l; intros kel.
  apply cps_ex_l; intros data.
  apply cps_ex_l; intros rows.
  apply cps_ex_l; intros x0.
  apply cps_ex_l; intros f0.
  apply cps_ex_l; intros f1.
  apply cps_ex_l; intros f2.
  apply cps_ex_l; intros f3.
  apply cps_ex_l; intros f4.
  apply cps_ex_l; intros js.
  apply cps_ex_l; intros j0.
  apply cps_ex_l; intros j1.
  apply cps_ex_l; intros r1.
  apply cps_ex_l; intros r5.
  apply cps_ex_l; intros r6.
  apply cps_ex_l; intros r7.
  apply cps_ex_l; intros r10.
  apply cps_ex_l; intros r11.
  apply cps_ex_l; intros r12.
  apply cps_ex_l; intros r13.
  apply cps_ex_l; intros r14.
  apply cps_ex_l; intros r15.
  apply cps_ex_l; intros r16.
  apply cps_ex_l; intros r17.
  apply cps_ex_l; intros r28.
  apply cps_ex_l; intros r29.
  apply cps_ex_l; intros r30.
  apply cps_ex_l; intros r31.
  apply cps_ex_l; intros F'.
  apply cps_ex_l; intros fc'.
  apply cps_and_pure_r; intros (KE & IB & JB & LCTX & ART1 & MI1 & WM1 & ST1 & FR & FLO & PVC & FHI & FSH & LH & SSP & AGF & POBJ & KOBJ & LV & FRS & SP0S & CRS).
  destruct LCTX as (CTX & D8 & HOK & H3 & W3 & WH & LVB & CRB).
  pose proof CTX as (FDO & MST & ART0 & POBJ0 & LOW & LOR & LO0 & SPT & SPA & SPB & LVP & FRB & DNZ & FR0 & FR64 & NFA).
  unfold kfp_stack_16 in FR. unfold kfp_frame_lo in FLO. unfold kfp_fshadow in FSH.
  destruct (af_client_consts RT AF S0 m0 ART1) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF S0 m0 ART1) as SP0R. pose proof (af_sp0_win RT AF S0 m0 ART1) as SP0W.
  rewrite SP0S in SP0R, SP0W.
  unfold entry_st, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  set (PF := kfp_PF RT Σ usp) in *.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a Ha. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [HH|HH]; [left; exact HH| right; unfold STACK_WIN in HH; lia]. }
  pose proof ST1 as (STa & STb & _).
  pose proof (af_frames_range RT AF S0 m0 fr 1%nat ART1 ltac:(rewrite FRS; left; reflexivity)) as (FRA0 & FRHI & _ & _).
  pose proof (af_frames_align RT AF S0 m0 fr 1%nat ART1 ltac:(rewrite FRS; left; reflexivity)) as (FRA64 & FRSEG).
  pose proof (af_frames_hi RT AF S0 m0 fr 1%nat ART1 ltac:(rewrite FRS; left; reflexivity)) as FRSH.
  change (fs_size 1) with 128 in FRHI, FRSH. rewrite SP0S in FRHI. unfold STACK_WIN, SEGTOP_A in FRHI, FRSEG.
  (* [comment removed for export] *)
  park_disj.
  walk_to AF MST [(usp - 144, usp)] [e_stack_malloc 1%nat; e_returnErrorPtr; e_lept_stderr; e_kernelCreate; e_pixGetPixel; e_kernelSetElement; 0x923b8].
  idtac "L1-WALK".
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  pose proof FSH as SV. split_at SV 10%nat SV2. split_at SV2 1%nat SV3. clear SV SV3.
  idtac "L2-SV".
  (* [comment removed for export] *)
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
  idtac "L3-ATCALL".
  pose proof GPX as GX. unfold pixGetPixel_cps in GX.
  eapply cps_seq.
  { eapply GX with (lo := lo) (pix := pix) (v := v) (cv := cv) (x := j) (y := i) (pv := fr + 80) (x0 := x0); rt_side idtac.
    1: (apply (km_pix_obj_mono (rt_live RT Σ)); [intros e He; rewrite LV; apply km_live_in_old; exact He| exact POBJ]).
    1: (unfold optrF, own_frame; split;
        [ exists fr, 1%nat; split; [rewrite FRS; left; reflexivity|];
          change (fs_size 1) with 128;
          split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
          split; [lia|]; split; [lia|];
          replace (shad (fr + 80)) with (fr / 8 + 2147450890) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
          destruct SV2 as [[_ B] _]; exact B
        | unfold SEGTOP_A; unfold parked in FRSH; clear - FRA0 FR64 FRSH FRSEG; repeat split; first [lia | Z.div_mod_to_equations; lia] ]).
    1: lenv_tac.
    1: (pose proof (km_cost_bound (p_h v) (p_w v) H3 W3 WH) as KCB;
        pose proof KOBJ as (_ & _ & _ & _ & LEN & _);
        unfold lres; rewrite FRS, LV; unfold km_live; rewrite length_app, length_rev, length_map; cbn [length];
        split; [lia| split; [lia| split; [lia| ]]];
        intros p n Hin; apply in_app_or in Hin as [Hin|[Hin|[Hin|Hin]]];
        [ apply in_rev in Hin; apply in_map_iff in Hin as (r & Er & _); injection Er as _ <-; lia
        | injection Hin as _ <-; lia | injection Hin as _ <-; lia | exact (LVP p n Hin) ]). }
  idtac "L3-CALL".
  after_call RT AF.
  idtac "L4-AFTER".
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  pose proof (af_frames_range RT AF S0 m0 fr 1%nat ART1 ltac:(rewrite FRS; left; reflexivity)) as (_ & _ & _ & FLV).
  change (fs_size 1) with 128 in FLV.
  lazymatch goal with AGx : agree_on _ m0 ?m1 |- _ =>
    assert (KLp : keeps_live (rt_live RT S0) m0 m1)
      by (intros bb kk Hin a Ha; apply AGx; split;
          [ right; right; left; exists bb, kk; split; [repeat match goal with H : rt_live _ _ = rt_live RT S0 |- _ => rewrite H end; exact Hin| exact Ha]
          | cbn [outside]; split; [| exact I]; pose proof (FLV bb kk Hin); lia ]);
    pose proof (kel_obj_keep _ m0 m1 kel (p_h v) (p_w v) 2 2 data rows KLp KOBJ) as KOBJ1;
    assert (POBJ1 : pix_obj (rt_live RT Σ) m1 pix v cv)
      by (apply (pix_obj_keep _ m0 m1 pix v cv); [| exact POBJ];
          intros bb kk Hin; apply KLp; rewrite LV; apply km_live_in_old; exact Hin) end.
  clear KOBJ POBJ.
  idtac "L4C-OBJ".
  fold_ag ltac:(fun Hx => split;
    [ apply (aclient_mono _ _ usp _ _ _ _ Hx);
      [ intros e He; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; apply km_live_in_old; exact He
      | solve [frames_sub_tac] | lia ]
    | cbn [outside]; destruct (NFA _ Hx) as [N1 N2]; split; [lia| exact I] ]).
  idtac "L4-FOLD".
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  pose proof KOBJ1 as (_ & _ & _ & _ & LEN & _).
  destruct (nth_error rows (Z.to_nat i)) as [r|] eqn:NR; [| apply nth_error_None in NR; lia].
  pose proof (nth_error_In _ _ NR) as RIN.
  assert (RLV : In (r, 4 * p_w v) (rt_live RT S0)) by (rewrite LV; apply km_live_in_row; exact RIN).
  pose proof (FLV r (4 * p_w v) RLV) as RFR.
  pose proof (af_fshadow_apart RT AF S0 m0 fr 1%nat ART1 ltac:(rewrite FRS; left; reflexivity)) as (RFS & _).
  specialize (RFS r (4 * p_w v) RLV). change (fs_size 1) with 128 in RFS. unfold shad, SHB in RFS.
  pose proof (af_live_range RT AF S0 m0 r (4 * p_w v) ART1 RLV) as (_ & RR1 & RR2).
  pose proof (gp_live_hi RT GP S0 m0 r (4 * p_w v) ART1 RLV) as RR3.
  unfold STACK_WIN, SEGTOP_A in RR1, RR2. rewrite SP0S in RR1.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  idtac "L5-FACTS".
  walk_to AF MST [(usp - 144, usp)] [e_stack_malloc 1%nat; e_returnErrorPtr; e_lept_stderr; e_kernelCreate; e_pixGetPixel; e_kernelSetElement; 0x923b8].
  idtac "L5-WALK".
  (* [comment removed for export] *)
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
  idtac "L6-ATCALL".
  pose proof KSEO as KS. unfold kernelSetElement_obj_cps in KS.
  eapply cps_seq.
  { eapply KS with (lo := lo) (kel := kel) (sy := p_h v) (sx := p_w v) (cy := 2) (cx := 2) (data := data) (rows := rows) (i := i) (j := j) (r := r);
      rt_side idtac.
    all: lazymatch goal with
         | |- kel_obj _ _ _ _ _ _ _ _ _ =>
             first [ exact KOBJ1 | match goal with H : rt_live RT ?X = rt_live RT ?Y |- kel_obj (rt_live RT ?X) _ _ _ _ _ _ _ _ => rewrite H; exact KOBJ1 end ]
         | |- nth_error _ _ = _ => exact NR
         | |- lenv _ _ _ _ _ _ => lenv_tac
         | |- ?g => idtac "LEFT-KS:" g
         end. }
  idtac "L6-CALL".
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  assert (ROLD : forall b kk, In (b, kk) (rt_live RT Σ) -> r + 4 * p_w v <= b \/ b + kk <= r).
  { intros b kk Hb.
    assert (Hr : In (r, 4 * p_w v) (rev (map (fun r0 => (r0, 4 * p_w v)) rows)))
      by (apply in_rev; rewrite rev_involutive; apply in_map_iff; exists r; split; [reflexivity| exact RIN]).
    destruct (in_split _ _ Hr) as (l1 & l2 & E).
    apply (af_live_disj RT AF S0 m0 r (4 * p_w v) b kk l1 (l2 ++ (data, 8 * p_h v) :: (kel, 24) :: rt_live RT Σ) ART1).
    - rewrite LV. unfold km_live. rewrite E. rewrite <- app_assoc. reflexivity.
    - apply in_or_app. right. apply in_or_app. right. right. right. exact Hb. }
  idtac "L7-ROLD".
  try (unfold parked in RFR). try (unfold parked in RFS).
  after_call RT AF.
  idtac "L7-AFTER".
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with AGx : agree_on _ ?m1 ?m2, KO : kel_obj _ ?m2 kel _ _ _ _ _ _ |- _ =>
    assert (POBJ2 : pix_obj (rt_live RT Σ) m2 pix v cv)
      by (apply (pix_obj_keep _ m1 m2 pix v cv); [| exact POBJ1];
          intros bb kk Hin a Ha; apply AGx; split;
          [ right; right; left; exists bb, kk; split;
            [ repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; apply km_live_in_old; exact Hin
            | exact Ha ]
          | cbn [outside]; split; [| exact I]; pose proof (ROLD bb kk Hin); lia ]);
    rename KO into KOBJ2 end.
  clear POBJ1 KOBJ1.
  idtac "L8-OBJ".
  (* [comment removed for export] *)
  assert (RPF : forall z, PF z -> z < r \/ r + 4 * p_w v <= z).
  { intros z Hz. unfold PF, kfp_PF, aclient in Hz. unfold USTACK_TOP in Hz.
    destruct Hz as [Hs|[Hs|[Hs|[Hs|Hs]]]].
    - lia.
    - pose proof (client_static_below _ Hs). pose proof (client_static_ge _ Hs). unfold SEGTOP_A in *. unfold parked in RR2. lia.
    - destruct Hs as (b & kk & Hb & Hr). pose proof (ROLD b kk Hb). lia.
    - destruct Hs as (f & kf & Hf & Hr).
      pose proof (af_frames_range RT AF S0 m0 f kf ART1 ltac:(rewrite FRS; right; exact Hf)) as (_ & _ & _ & FLV').
      pose proof (FLV' r (4 * p_w v) RLV). lia.
    - destruct Hs as (f & kf & Hf & Hr).
      pose proof (af_fshadow_apart RT AF S0 m0 f kf ART1 ltac:(rewrite FRS; right; exact Hf)) as (FS' & _).
      pose proof (FS' r (4 * p_w v) RLV). lia. }
  idtac "L8-RPF".
  fold_ag ltac:(fun Hx => split;
    [ apply (aclient_mono _ _ usp _ _ _ _ Hx);
      [ intros e He; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; apply km_live_in_old; exact He
      | solve [frames_sub_tac] | lia ]
    | cbn [outside]; split; [| exact I]; pose proof (RPF _ Hx); lia ]).
  idtac "L8-FOLD".
  (* [comment removed for export] *)
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  walk_to AF MST [(usp - 144, usp)] [e_stack_malloc 1%nat; e_returnErrorPtr; e_lept_stderr; e_kernelCreate; e_pixGetPixel; e_kernelSetElement; 0x92508; 0x923b8; 0x924f0].
  idtac "L9-WALK".
  (* [comment removed for export] *)
  rewrite ?(bv_swrap_small 32 (j + 1)) by (change (bv_half_modulus 32) with (2^31); lia).
  rewrite ?(sx32_small (p_w v)) by lia.
  destruct (Z_lt_le_dec (j + 1) (p_w v)) as [JN|JE].
  { (* [comment removed for export] *)
    try brT.
    idtac "L10-A".
  (* [comment removed for export] *)
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I]).
    lazymatch goal with MUx : munch _ ?mm _ |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]) end.
    idtac "L11-ART".
    to_entry.
    assert (KN : k + 1 < p_w v * p_h v) by (rewrite KE; nia).
    apply cps_finish; intros c Hc. left. split; [exact KN|].
    unfold kfp_head_16. do 34 eexists. split; [exact Hc|].
    idtac "L11-HC".
  (* [comment removed for export] *)
    split; [lia|]. split; [lia|]. split; [lia|].
    split; [exact (conj CTX (conj D8 (conj HOK (conj H3 (conj W3 (conj WH (conj LVB CRB)))))))|].
    idtac "L12-A".
    split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    idtac "L12-B".
    split; [unfold kfp_stack_16; exact FR|].
    split; [unfold kfp_frame_lo; exact FLO|].
    split; [eassumption|]. split; [eassumption|].
    split; [unfold kfp_fshadow; exact FSH|].
    idtac "L12-C".
    split; [eassumption|]. split; [eassumption|]. split; [exact AGF|]. split; [exact POBJ2|].
    idtac "L12-D".
    lazymatch goal with |- ?g => idtac "G:" g end.
  (* [comment removed for export] *)
    split; [lazymatch goal with |- kel_obj (rt_live RT ?A) _ _ _ _ _ _ _ _ => match goal with H : rt_live RT A = _ |- _ => rewrite H end end; exact KOBJ2|].
    idtac "L13-KOBJ".
    repeat match goal with H : rt_live RT ?X = rt_live RT ?Y |- context [rt_live RT ?X] => rewrite H end.
    repeat match goal with H : rt_frames RT ?X = rt_frames RT ?Y |- context [rt_frames RT ?X] => rewrite H end.
    repeat match goal with H : rt_sp0 RT ?X = rt_sp0 RT ?Y |- context [rt_sp0 RT ?X] => rewrite H end.
    split; [first [exact LV | reflexivity]|]. split; [first [exact FRS | reflexivity]|]. split; [first [exact SP0S | reflexivity]|].
    idtac "L13-EQ".
    lazymatch goal with |- ?g => idtac "G:" g end.
  (* [comment removed for export] *)
    repeat match goal with H : rt_credit RT ?X = _ |- context [rt_credit RT ?X] => rewrite H end. lia.
  }
  idtac "L14-A-DONE".
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  try brF.
  awalk [e_stack_malloc 1%nat; e_returnErrorPtr; e_lept_stderr; e_kernelCreate; e_pixGetPixel; e_kernelSetElement; 0x92508; 0x923b8].
  idtac "L15-WALK".
  (* [comment removed for export] *)
  rewrite ?(bv_swrap_small 32 (i + 1)) by (change (bv_half_modulus 32) with (2^31); lia).
  rewrite ?(sx32_small (p_h v)) by lia.
  assert (JW : j + 1 = p_w v) by lia.
  destruct (Z_lt_le_dec (i + 1) (p_h v)) as [IN|IE].
  { (* [comment removed for export] *)
    try brF.
    awalk [e_stack_malloc 1%nat; e_returnErrorPtr; e_lept_stderr; e_kernelCreate; e_pixGetPixel; e_kernelSetElement; 0x92508; 0x923b8].
    idtac "L16-B1".
  (* [comment removed for export] *)
    rewrite ?(sx32_small (p_w v)) by lia. try brF.
    awalk [e_stack_malloc 1%nat; e_returnErrorPtr; e_lept_stderr; e_kernelCreate; e_pixGetPixel; e_kernelSetElement; 0x92508; 0x923b8].
    idtac "L17-B1".
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I]).
    lazymatch goal with MUx : munch _ ?mm _ |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]) end.
    to_entry.
    assert (KN : k + 1 < p_w v * p_h v) by (rewrite KE; nia).
    apply cps_finish; intros c Hc. left. split; [exact KN|].
    unfold kfp_head_16. do 34 eexists. split; [exact Hc|].
    idtac "L17-HC".
    split; [nia|]. split; [lia|]. split; [lia|].
    split; [exact (conj CTX (conj D8 (conj HOK (conj H3 (conj W3 (conj WH (conj LVB CRB)))))))|].
    split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    split; [unfold kfp_stack_16; exact FR|].
    split; [unfold kfp_frame_lo; exact FLO|].
    split; [eassumption|]. split; [eassumption|].
    split; [unfold kfp_fshadow; exact FSH|].
    split; [eassumption|]. split; [eassumption|]. split; [exact AGF|]. split; [exact POBJ2|].
    split; [lazymatch goal with |- kel_obj (rt_live RT ?A) _ _ _ _ _ _ _ _ => match goal with H : rt_live RT A = _ |- _ => rewrite H end end; exact KOBJ2|].
    repeat match goal with H : rt_live RT ?X = rt_live RT ?Y |- context [rt_live RT ?X] => rewrite H end.
    repeat match goal with H : rt_frames RT ?X = rt_frames RT ?Y |- context [rt_frames RT ?X] => rewrite H end.
    repeat match goal with H : rt_sp0 RT ?X = rt_sp0 RT ?Y |- context [rt_sp0 RT ?X] => rewrite H end.
    split; [first [exact LV | reflexivity]|]. split; [first [exact FRS | reflexivity]|]. split; [first [exact SP0S | reflexivity]|].
    repeat match goal with H : rt_credit RT ?X = _ |- context [rt_credit RT ?X] => rewrite H end. lia.
  }
  idtac "L17-B1-DONE".
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  try brT.
  cps_stop.
  art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I]).
  lazymatch goal with MUx : munch _ ?mm _ |- _ =>
    agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]) end.
  to_entry.
  assert (KX : k + 1 = p_w v * p_h v) by (rewrite KE; nia).
  pose proof (km_cost_bound (p_h v) (p_w v) H3 W3 WH) as KCB.
  idtac "L18-EXITSTATE".
  lazymatch goal with |- cps _ (ASTA RT ?S _ (eq (entry_st ?a1 _ _ _ ?a5 ?a6 ?a7 _ _ ?a10 ?a11 ?a12 ?a13 ?a14 ?a15 ?a16 ?a17 _ ?a19 _ ?a21 ?a22 ?a23 ?a24 ?a25 _ _ ?a28 ?a29 ?a30 ?a31 ?FF ?fcc _ ?mm))) _ =>
    eapply (cps_conseq _ _ _ _ _ (EXIT S mm kel (Z_to_bv 64 1102416563)
                                  js j0 j1
                                  a1 a5 a6 a7 a10 a11 a12 a13 a14 a15 a16 a17 a19 a21 a22 a23 a24 a25 a28 a29 a30 a31 FF fcc CTX
                                  ltac:(eassumption) ltac:(eassumption) ltac:(eassumption) ltac:(eassumption)
                                  ltac:(unfold kfp_stack_16; exact FR) (rw_cells_head _ _ _ _ FLO) ltac:(unfold kfp_fshadow; exact FSH)
                                  ltac:(eassumption) ltac:(eassumption) AGF _ _ _ _ _))
  end.
  idtac "L18-EXIT".
  Unshelve.
  (* [comment removed for export] *)
  1: (intros c Hc; exact Hc).
  1: (intros c Hc; subst QF; cbv beta; right; split; [exact KX| exact Hc]).
  1: (repeat match goal with H : rt_frames RT ?X = rt_frames RT ?Y |- context [rt_frames RT ?X] => rewrite H end; first [exact FRS | reflexivity]).
  1: (repeat match goal with H : rt_sp0 RT ?X = rt_sp0 RT ?Y |- context [rt_sp0 RT ?X] => rewrite H end; first [exact SP0S | reflexivity]).
  1: (repeat match goal with H : rt_credit RT ?X = _ |- context [rt_credit RT ?X] => rewrite H end; lia).
  1: (apply (km_pix_obj_mono (rt_live RT Σ)); [| exact POBJ2]; intros e He;
      repeat match goal with H : rt_live RT ?X = rt_live RT ?Y |- context [rt_live RT ?X] => rewrite H end;
      rewrite LV; apply km_live_in_old; exact He).
  1: (right; exists data, rows; split; [exact D8|]; split;
      [ lazymatch goal with |- kel_obj (rt_live RT ?A) _ _ _ _ _ _ _ _ => match goal with H : rt_live RT A = _ |- _ => rewrite H end end; exact KOBJ2
      | repeat match goal with H : rt_live RT ?X = rt_live RT ?Y |- context [rt_live RT ?X] => rewrite H end; exact LV ]).
Qed.

Lemma kfp_loop_ok_16 : kfp_exit_stmt_16 RT Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m pix v cv fr ->
  forall k, 0 <= k < p_w v * p_h v ->
  cps asegs (kfp_head_16 RT Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m pix v cv fr k)
            (kfp_post RT Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m pix v cv).
Proof using AF RC GP GPX KSEO.
  intros EXIT. apply (cps_loop_Z (kfp_head_16 RT Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m pix v cv fr)
                                (kfp_post RT Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m pix v cv) (p_w v * p_h v)).
  exact (kfp_step_ok_16 EXIT).
Qed.
End KFP_LOOP.
