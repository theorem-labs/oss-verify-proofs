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
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.A21 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit Lept_chain Lept_leaf LeptC_leaf LeptL_kit Lept_objkit Pm_iface Pm_iface2 Pm_okit Pm_livekit D_iface D_defs.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* [comment removed for export] *)
Ltac shbr8z :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if ?c then Z_to_bv 64 ?SLOW else Z_to_bv 64 ?FAST) ?fc ?rv ?mm ?ro) =>
      let b := shbyte_of c in
      lazymatch goal with
      | K : shk mm b ?X |- _ =>
          let OK := fresh "SHOK" in
          first [ match goal with
                  | ACC : acc asegs mm ?a ?n |- _ => assert (OK : sh_ok b (X + 8 - 1)) by (apply (shk_ok mm a n X 8 b ACC K); lia)
                  end
                | fail 1 "shbr8z: cannot prove the 8-byte access addressable:" X ];
          apply sh_ok_8 in OK; [ | lia ];
          rewrite ?(sxb_small b) by lia;
          rewrite OK; brF; clear K OK
      end
  end.

Section CC.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis RERR : returnError_cps RT e_returnErrorInt.
Hypothesis VALID : pixcmapIsValid_cps RT.
Hypothesis CMCOPY : pixcmapCopy_cps RT.

Theorem pixCopyColormap_ok : pixCopyColormap_cps RT.
Proof using AF GP RERR VALID CMCOPY.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pixd pixs vd v cv ras
    FDO MST -> -> -> PS PD PCMD0 PDATD DEQ NEQ UCTX TRC ENV RES.
  unfold lpost, lenv, lres, keeps, keepsL in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct RES as (FRB & LVB & CRB & LVP).
  (* [comment removed for export] *)
  destruct PS as (PXSC & (INS & PS0 & PS16 & _) & HOKS & _ & PCMS).
  pose proof PD as (PXDC & (IND & PD0 & PD16 & _) & HOKD & DATD & _).
  unfold pix_cells in PXSC, PXDC. rewrite PCMD0 in PXDC.
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, e_pixCopyColormap, PMCOPY_CALLOC1, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  unfold uctx in UCTX.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold LSTK, STDERR_STACK in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  pose proof ST as (STa & STb & _).
  lib_refresh RT GP.
  pose proof RERR as RE. unfold returnError_cps in RE. pose proof VALID as VLD. unfold pixcmapIsValid_cps in VLD.
  pose proof CMCOPY as CPY. unfold pixcmapCopy_cps in CPY.
  set (PF := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a /\ outside [(pixd + 48, pixd + 56)] a).
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a [Ha _]. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]. }
  chunk_facts RT AF GP pixd 64. chunk_facts RT AF GP pixs 64.
  pose proof (live_apart RT AF Σ m pixd 64 pixs 64 ART0 IND INS NEQ) as DSA.
  assert (AL : usp mod 32 = 0 \/ usp mod 32 = 16) by (Z.div_mod_to_equations; lia).
  (* [comment removed for export] *)
  hide NEQ. hide PDATD. hide PCMS. hide DATD. hide PD. hide HOKS. hide HOKD.
  park_disj.
  destruct AL as [AL|AL].
  - (* [comment removed for export] *)
    carve_frame 96%nat ST.
    clear_acc.
    walk_to AF MST [(usp - 96, usp)] [0x4896c].
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                  ltac:(fun Hx => cbn [outside]; split; [destruct (PFS _ Hx); lia| exact I]).
    eapply cps_seq.
    { eapply (gp_stack_malloc_1 RT GP) with (lo := lo); rt_side idtac. }
    after_call RT AF.
    fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [auto| auto| lia]).
    fframe_open RT AF PF (rt_live RT Σ) usp 1%nat 128 ltac:(fun Ha => exact (proj1 Ha)).
    fframe_chunk RT AF fr 1%nat 128 pixd 64.
    fframe_chunk RT AF fr 1%nat 128 pixs 64.
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. clear_acc. park_disj.
    walk_to AF MST [(usp - 96, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x8fa24].
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
    lazymatch goal with MUx : munch _ ?mm _ |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                         repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *.
    (* [comment removed for export] *)
    lazymatch goal with FRx : rw_cells asegs _ (usp + -96) ?cs |- _ =>
      assert (EPI : forall (S : rts RT) (mE : mem) (rv : word) (cmapd : Z) (cv' : cmapv)
                (r1 r5 r6 r7 r9 r11 r12 r13 r14 r15 r16 r17 r19 r20 r21 r24 r25 r28 r29 r30 r31 : word) F' fc',
          ART RT S mE -> mem_inv asegs mE -> stk asegs mE lo (usp + -96) -> rw_cells asegs mE (usp + -96) cs ->
          wr_at asegs mE fr 120 -> wr_at asegs mE (fr / 8 + 2147450880) 16 ->
          LIBH mE -> io_ssp mE -> agree_on PF m mE -> wmono asegs m mE ->
          rt_frames RT S = (fr, 1%nat) :: rt_frames RT Σ -> rt_sp0 RT S = rt_sp0 RT Σ -> rt_credit RT Σ - 16 <= rt_credit RT S ->
          (forall e, In e (rt_live RT Σ) -> In e (rt_live RT S)) ->
          rw_cells asegs mE pixd (pix_cells (pixv_cmap vd cmapd)) ->
          ((cmapd = 0 /\ rt_live RT S = rt_live RT Σ)
           \/ (cmapd <> 0 /\ cmap_obj (rt_live RT S) mE cmapd cv'
               /\ cmapd <> pixd /\ c_arr cv' <> pixd /\ cmapd <> p_data vd /\ c_arr cv' <> p_data vd
               /\ p_cmap v <> 0 /\ c_depth cv' = c_depth cv /\ c_nalloc cv' = c_nalloc cv /\ c_n cv' = c_n cv
               /\ rt_live RT S = (c_arr cv', 4 * c_nalloc cv') :: (cmapd, 24) :: rt_live RT Σ)) ->
          cps asegs (ASTA RT S PMc (eq (entry_st r1 (Z_to_bv 64 (usp + -96)) gp (Z_to_bv 64 TP_A) r5 r6 r7 (Z_to_bv 64 usp) r9
                                          rv r11 r12 r13 r14 r15 r16 r17 (Z_to_bv 64 fr) r19 r20 r21 (Z_to_bv 64 (fr / 8 + 2147450880))
                                          (Z_to_bv 64 fr) r24 r25 s10 s11 r28 r29 r30 r31 F' fc' 0x8fcbc mE))) QF) end.
    { intros S mE rv cmapd cv' r1 r5 r6 r7 r9 r11 r12 r13 r14 r15 r16 r17 r19 r20 r21 r24 r25 r28 r29 r30 r31 F' fc'
        ARTE MIE STE FRE WFE WSE LHE SSPE AGE WME EFR ESP0 ECR LSUB PXE PAY.
      clear AGF. rename AGE into AGF.
      repeat match goal with H : rw_cells asegs _ _ _ |- _ => lazymatch H with FRE => fail | PXE => fail | _ => clear H end end.
      repeat match goal with H : ro_cells asegs _ _ _ |- _ => clear H end.
      repeat match goal with H : ART RT _ _ |- _ => lazymatch H with ARTE => fail | _ => clear H end end.
      repeat match goal with H : LIBH _ |- _ => lazymatch H with LHE => fail | _ => clear H end end.
      repeat match goal with H : io_ssp _ |- _ => lazymatch H with SSPE => fail | _ => clear H end end.
      repeat match goal with H : stk asegs _ _ _ |- _ => lazymatch H with STE => fail | _ => clear H end end.
      repeat match goal with H : mem_inv asegs _ |- _ => lazymatch H with MIE => fail | _ => clear H end end.
      repeat match goal with H : wmono asegs _ _ |- _ => lazymatch H with WME => fail | _ => clear H end end.
      repeat match goal with H : munch _ _ _ |- _ => clear H end.
      repeat match goal with H : rt_frames RT _ = _ |- _ => lazymatch H with EFR => fail | _ => clear H end end.
      repeat match goal with H : rt_live RT _ = _ |- _ => clear H end.
      repeat match goal with H : rt_sp0 RT _ = _ |- _ => lazymatch H with ESP0 => fail | _ => clear H end end.
      repeat match goal with H : rt_credit RT _ = _ |- _ => clear H end.
      clear_acc.
      destruct (wr_at_rw_CB mE fr 120 WFE ltac:(lia)) as (jfE & FRME). destruct (wr_at_rw_CB mE (fr / 8 + 2147450880) 16 WSE ltac:(lia)) as (jsE & FSHE).
      change (Z.to_nat 120) with 120%nat in FRME. change (Z.to_nat 16) with 16%nat in FSHE.
      (* [comment removed for export] *)
      assert (LOUT : forall b k, In (b, k) (rt_live RT S) -> forall x, b <= x < b + k ->
                outside [(usp - 96, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] x).
      { intros bb kk Hb zz Hz.
        pose proof (af_live_range RT AF S mE bb kk ARTE Hb) as LR.
        pose proof (af_frames_range RT AF S mE fr 1%nat ARTE ltac:(rewrite EFR; left; reflexivity)) as (_ & _ & _ & D1). specialize (D1 bb kk Hb).
        pose proof (af_fshadow_apart RT AF S mE fr 1%nat ARTE ltac:(rewrite EFR; left; reflexivity)) as (D2 & _). specialize (D2 bb kk Hb).
        change (fs_size 1) with 128 in D1, D2. unfold shad, SHB in D2. rewrite ESP0 in LR. unfold STACK_WIN in LR.
        cbn [outside]. clear - LR D1 D2 Hz LOW LOR. repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]. }
      hide PAY. hide LOUT. hide LSUB.
      hide PXE. (* [comment removed for export] *)
      unfold entry_st.
      walk_to AF MST [(usp - 96, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x8fd18].
      lazymatch goal with MUx : munch _ mE ?mc |- _ =>
        assert (KEEP1 : keeps_live (rt_live RT S) mE mc)
          by (unfold hid in LOUT; let bb := fresh "bb" in let kk := fresh "kk" in let Hb := fresh "Hb" in let a := fresh "a" in let Ha := fresh "Ha" in
              intros bb kk Hb a Ha; apply MUx; exact (LOUT bb kk Hb _ Ha)) end.
      frame_release RT AF GP MST Σ fr 1%nat 128 PF AGF PFS usp lo 0x8fd20
        ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
        ltac:(fun Hx => let N1 := fresh "N1" in let N2 := fresh "N2" in
                        cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                        repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
      walk_to AF MST [(usp - 96, usp)] (@nil Z).
      cps_stop.
      try (lazymatch goal with STx : stk asegs _ lo (usp + -96) |- _ => release_frame FRE STx usp end).
      art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I]).
      lazymatch goal with MUx : munch _ ?mm ?mc |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
        assert (KEEP3 : keeps_live (rt_live RT S) mm mc)
          by (unfold hid in LOUT; let bb := fresh "bb" in let kk := fresh "kk" in let Hb := fresh "Hb" in let a := fresh "a" in let Ha := fresh "Ha" in
              intros bb kk Hb a Ha; apply MUx; cbn [outside]; split; [exact (proj1 (LOUT bb kk Hb _ Ha))| exact I]);
        agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]) end.
      lazymatch goal with K3 : keeps_live _ _ ?mc |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
        assert (KEEPF : keeps_live (rt_live RT S) mE mc)
          by (eapply keeps_live_trans; [exact KEEP1|]; eapply keeps_live_trans; [exact KEEPR| exact K3]) end.
      unfold hid in LSUB, PAY, DATD, HOKD, PXE.
      assert (PINS : In (pixd, 64) (rt_live RT S)) by (exact (LSUB _ IND)).
      apply cps_finish. intros c0 Hc. subst QF. cbv beta.
      lazymatch type of Hc with ASTA RT ?S' _ _ _ => exists S', rv, cmapd, cv' end.
      split.
      { eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-. eexists.
        split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
        split; [split; [split; [assumption| split; [assumption| split; [| assumption]]]| split; assumption]|].
        { lazymatch goal with WMx : wmono asegs m ?mf |- wmono asegs m ?mf => exact WMx end. }
        split; [intros xa HXa HXo; apply AGF; split; [exact HXa| exact HXo]|].
        split.
        - (* [comment removed for export] *)
          rewrite LV2. unfold pix_obj.
          split; [apply (keeps_live_cells (rt_live RT S) mE _ pixd 64 pixd _ KEEPF PINS); [lia| cbn; lia| exact PXE]|].
          split; [split; [exact PINS| split; [exact PD0| split; [exact PD16| lia]]]|].
          split; [exact HOKD|].
          split.
          + cbn [p_data pixv_cmap]. destruct DATD as [DZ|((DIN & DR) & DNE)]; [left; exact DZ| right].
            split; [split; [exact (LSUB _ DIN)| exact DR]| exact DNE].
          + cbn [p_cmap p_data pixv_cmap]. destruct PAY as [(E0 & _)|(NE0 & CMO & N1 & N2 & N3 & N4 & _)]; [left; exact E0| right].
            split; [exact (cmap_obj_keep _ mE _ cmapd cv' KEEPF CMO)|]. repeat split; assumption.
        - intros NE0. destruct PAY as [(E0 & _)|(_ & _ & _ & _ & _ & _ & PCN & E1 & E2 & E3 & _)]; [contradiction|]. repeat split; assumption. }
      rewrite LV2, FRS2, SP2, CR2.
      split; [| split; [reflexivity| split; [exact ESP0| lia]]].
      destruct PAY as [(E0 & EL)|(NE0 & PAYR)].
      - rewrite E0. change (0 =? 0) with true. cbv iota. exact EL.
      - replace (cmapd =? 0) with false by (symmetry; apply Z.eqb_neq; exact NE0).
        destruct PAYR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & EL). exact EL. }

    assert (DRS : 1 <= p_d v <= 32) by (unfold hid in HOKS; destruct HOKS as (HDP & _); clear - HDP; cbn [In] in HDP; lia).
    pose proof NEQ as NEQ1. unfold hid in NEQ1.
    walk_to AF MST [(usp - 96, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16); (pixd + 48, pixd + 56)] [0x8fa64].
    cwalk [0x8fa64].
    clear NEQ1. clear_acc.
    cwalk [0x8fa68].
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac|
                         split; [intros zz Hzz; right; right; left; exists pixd, 64; split; [solve [in_live_tac]| lia]| exact I]]]]).
    lazymatch goal with MUx : munch _ ?mm _ |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; destruct Hx as [_ Hx2]; cbn [outside] in Hx2;
                                         unfold shad, SHB in *; repeat split; try exact I; first [tauto | lia | Z.div_mod_to_equations; lia]) end.
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *.
    walk_to AF MST [(usp - 96, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16); (pixd + 48, pixd + 56)] [0x8faa4].
    clear_acc.
    cwalk [0x8faa8].
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac|
                         split; [intros zz Hzz; right; right; left; exists pixd, 64; split; [solve [in_live_tac]| lia]| exact I]]]]).
    lazymatch goal with MUx : munch _ ?mm _ |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; destruct Hx as [_ Hx2]; cbn [outside] in Hx2;
                                         unfold shad, SHB in *; repeat split; try exact I; first [tauto | lia | Z.div_mod_to_equations; lia]) end.
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *.
    walk_to AF MST [(usp - 96, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16); (pixd + 48, pixd + 56)] [0x91944; 0x8fcbc].
    unfold hid in PCMS. destruct PCMS as [PCZ | (CMO & NC1 & NC2 & NC3 & NC4)].
    + (* [comment removed for export] *)
      rewrite PCZ in *.
      brT. cwalk [0x8fcbc].
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac|
                         split; [intros zz Hzz; right; right; left; exists pixd, 64; split; [solve [in_live_tac]| lia]| exact I]]]]).
    lazymatch goal with MUx : munch _ ?mm _ |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; destruct Hx as [_ Hx2]; cbn [outside] in Hx2;
                                         unfold shad, SHB in *; repeat split; try exact I; first [tauto | lia | Z.div_mod_to_equations; lia]) end.
    to_entry.
        eapply EPI with (cmapd := 0) (cv' := mkCmapv 0 0 0 0); try eassumption.
        all: lazymatch goal with
             | |- wr_at asegs _ _ 120 => first [eassumption | exact (proj2 FRM)]
             | |- wr_at asegs _ _ 16 => exact (proj2 FSH)
             | |- rw_cells asegs _ _ (pix_cells _) => unfold pix_cells, pixv_cmap; cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data]; exact PXDC
             | |- _ <= _ => repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end; lia
             | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
             | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
             | |- forall e, In e _ -> In e _ => solve [live_add_tac]
             | |- _ \/ _ => left; split; [reflexivity| repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity]
             | |- ?g => idtac "LEFTOVER:" g
             end.
    + (* [comment removed for export] *)
      clear NC1 NC2 NC3 NC4.
      pose proof CMO as ((pad & CMC) & (INC & CM0 & CM16 & _) & (INA & AR0 & AR16 & ARN) & CMOK & NEQA). clear pad CMC. hide NEQA.
      assert (CMNE : p_cmap v <> pixd) by (apply (live_size_ne RT AF Σ m (p_cmap v) 24 pixd 64 ART0 INC IND); lia).
      pose proof (live_apart RT AF Σ m (p_cmap v) 24 pixd 64 ART0 INC IND CMNE) as CMD. clear CMNE.
      (* [comment removed for export] *)
      assert (KCM : forall mc, agree_on PF m mc -> keeps_live [(p_cmap v, 24)] m mc).
      { intros mc AG. apply (keeps_live_of_agree (rt_live RT Σ) (rt_frames RT Σ) usp [(pixd + 48, pixd + 56)] m mc _ AG).
        - intros e [<-|[]]. exact INC.
        - intros bq kq zq [Eq|[]] Hzq. injection Eq as <- <-. cbn [outside]. split; [| exact I]. clear - CMD Hzq. lia. }
      park CMD.
      assert (PCNZ : p_cmap v <> 0) by lia.
      chunk_facts RT AF GP (p_cmap v) 24. park_disj.
      brF. hide PCNZ.
      cwalk [0x91944; 0x8fcbc].
      (* [comment removed for export] *)
      split_last_CB FRM [24; 4; 4]%nat. split_at FRM 6%nat FRv. split_at FRv 1%nat FRrest.
      destruct (cb4_c4 _ _ _ FRv) as (v0 & VC0). clear FRv.
      pose proof FSH as T1; split_at T1 14%nat SHV; split_at SHV 1%nat T3; clear T1 T3.
      at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac|
                           split; [intros zz Hzz; right; right; left; exists pixd, 64; split; [solve [in_live_tac]| lia]| exact I]]]])
                    ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; destruct Hx as [_ Hx2]; cbn [outside] in Hx2;
                                    unfold shad, SHB in *; repeat split; try exact I; first [tauto | lia | Z.div_mod_to_equations; lia]).
      lazymatch goal with AGx : agree_on PF m ?mc |- _ => pose proof (cmap_obj_keep1 _ m mc _ cv (KCM mc AGx) CMO) as CMOc end.
      eapply cps_seq.
      { eapply VLD with (lo := lo) (cmap := p_cmap v) (pix := 0) (pv := fr + 112) (cv := cv) (v := mkPixv 0 0 0 0 0 0 0 0 0 0 0) (x := v0); rt_side idtac.
        all: lazymatch goal with
             | |- cmap_obj _ _ _ _ => repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact CMOc
             | |- _ \/ _ => left; reflexivity
             | |- optrF _ _ _ _ _ =>
                 unfold optrF, own_frame; unfold parked in *; split;
                 [ exists fr, 1%nat; change (fs_size 1) with 128;
                   split; [solve [frames_in_tac]|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
                   split; [lia|]; split; [ul|];
                   lazymatch type of SHV with rw_cells _ _ ?A _ => replace (shad (fr + 112)) with A by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia) end;
                   destruct SHV as [[_ B] _]; exact B
                 | split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|]; split; [lia| right; ul] ]
             | |- rw_cells _ _ _ [C4 _] => exact VC0
             | |- lenv _ _ _ _ _ _ => lenv_tac
             | |- lres _ _ _ _ _ => lres_tac
             | |- ?g => idtac "LEFTOVER:" g
             end. }
      after_call RT AF.
      fold_ag ltac:(fun Hx => pose proof (NFA _ Hx) as [N1 _]; destruct Hx as [Hx1 _];
                    first [ split; [apply (aclient_mono _ _ usp _ _ _ _ Hx1); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]
                                   | cbn [outside]; split; [lia| exact I]]
                          | apply (aclient_mono _ _ usp _ _ _ _ Hx1); [solve [live_sub_tac]| solve [frames_sub_tac]| lia] ]).
      refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. park_disj.
      lazymatch goal with H : rw_cells asegs _ (fr + 112) [C4 _] |- _ => rename H into VC1 end.
      (* [comment removed for export] *)
      lazymatch goal with F1 : rw_cells asegs ?mm fr _, F2 : rw_cells asegs ?mm (fr + 112) [C4 _], F3 : rw_cells asegs ?mm (fr + 116) _ |- _ =>
        assert (WF120 : wr_at asegs mm fr 120)
          by (apply (proj2 (wr_at_app mm fr 112 8 ltac:(lia) ltac:(lia))); split; [exact (proj2 F1)|];
              apply (proj2 (wr_at_app mm (fr + 112) 4 4 ltac:(lia) ltac:(lia))); split; [exact (proj2 F2)|];
              replace (fr + 112 + 4) with (fr + 116) by lia; exact (proj2 F3)) end.
      walk_to AF MST [(usp - 96, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16); (pixd + 48, pixd + 56)] [0x91680; 0x8d86c; 0x8fcbc].
      if_cases HV; clear HV.
      * (* [comment removed for export] *)
        cwalk [0x8d86c; 0x8fcbc].
      at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac|
                           split; [intros zz Hzz; right; right; left; exists pixd, 64; split; [solve [in_live_tac]| lia]| exact I]]]])
                    ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; destruct Hx as [_ Hx2]; cbn [outside] in Hx2;
                                    unfold shad, SHB in *; repeat split; try exact I; first [tauto | lia | Z.div_mod_to_equations; lia]).
        eapply cps_seq.
        { eapply RE with (lo := lo); rt_side idtac.
          all: lazymatch goal with
               | |- exists l, In _ LEPT_LITS => rewrite ?unsigned_lit by lia; lit_in
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- (_ < _)%nat => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; cbn [length]; unfold FRAMES_MAX in *; lia
               | |- _ <= rt_credit _ _ => repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end; lia
               | |- ?g => idtac "LEFTOVER:" g
               end. }
        after_call RT AF.
        fold_ag ltac:(fun Hx => destruct Hx as [Hx1 _]; apply (aclient_mono _ _ usp _ _ _ _ Hx1); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| lia]).
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. park_disj.
        walk_to AF MST [(usp - 96, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16); (pixd + 48, pixd + 56)] [0x8fcbc].
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac|
                         split; [intros zz Hzz; right; right; left; exists pixd, 64; split; [solve [in_live_tac]| lia]| exact I]]]]).
    lazymatch goal with MUx : munch _ ?mm _ |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; destruct Hx as [_ Hx2]; cbn [outside] in Hx2;
                                         unfold shad, SHB in *; repeat split; try exact I; first [tauto | lia | Z.div_mod_to_equations; lia]) end.
    to_entry.
        eapply EPI with (cmapd := 0) (cv' := mkCmapv 0 0 0 0); try eassumption.
        all: lazymatch goal with
             | |- wr_at asegs _ _ 120 => first [eassumption | exact (proj2 FRM)]
             | |- wr_at asegs _ _ 16 => exact (proj2 FSH)
             | |- rw_cells asegs _ _ (pix_cells _) => unfold pix_cells, pixv_cmap; cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data]; exact PXDC
             | |- _ <= _ => repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end; lia
             | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
             | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
             | |- forall e, In e _ -> In e _ => solve [live_add_tac]
             | |- _ \/ _ => left; split; [reflexivity| repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity]
             | |- ?g => idtac "LEFTOVER:" g
             end.
      * (* [comment removed for export] *)
        cwalk [0x91680; 0x8d86c; 0x8fcbc].
        assert (RA4096 : 4096 <= bv_unsigned ra < 2^64).
        { pose proof client_traces_wf as Wq. rewrite forallb_forall in Wq. specialize (Wq _ TRC).
          apply andb_prop in Wq. destruct Wq as [_ Wq]. cbn [forallb] in Wq.
          apply andb_prop in Wq. destruct Wq as [_ Wq]. apply andb_prop in Wq. destruct Wq as [Wq _].
          apply andb_prop in Wq. destruct Wq as [Wq _]. apply andb_prop in Wq. destruct Wq as [Wq1 Wq2].
          apply Z.leb_le in Wq1. apply Z.ltb_lt in Wq2. lia. }
      at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac|
                           split; [intros zz Hzz; right; right; left; exists pixd, 64; split; [solve [in_live_tac]| lia]| exact I]]]])
                    ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; destruct Hx as [_ Hx2]; cbn [outside] in Hx2;
                                    unfold shad, SHB in *; repeat split; try exact I; first [tauto | lia | Z.div_mod_to_equations; lia]).
        lazymatch goal with AGx : agree_on PF m ?mc |- _ => pose proof (cmap_obj_keep1 _ m mc _ cv (KCM mc AGx) CMO) as CMOd end.
        eapply cps_seq.
        { eapply CPY with (lo := lo) (cmaps := p_cmap v) (cv := cv) (ras := bv_unsigned ra :: ras); rt_side idtac.
          all: lazymatch goal with
               | |- cmap_obj _ _ _ _ => repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact CMOd
               | |- uctx _ _ _ _ =>
                   unfold uctx; rewrite ?unsigned_lit by lia;
                   lazymatch goal with |- chain_ok ?mc _ _ _ =>
                     let FRc := fresh "FRc" in let REC := fresh "REC" in
                     pose proof FR as FRc; split_before FRc (C8 s0) REC; clear FRc;
                     replace (C8 s0) with (C8 (Z_to_bv 64 (bv_unsigned s0))) in REC by (rewrite Z_to_bv_bv_unsigned; reflexivity);
                     replace (C8 ra) with (C8 (Z_to_bv 64 (bv_unsigned ra))) in REC by (rewrite Z_to_bv_bv_unsigned; reflexivity);
                     apply (chain_ok_push mc _ usp (bv_unsigned ra) (bv_unsigned s0) ras);
                     [ lia | clear - SPA; Z.div_mod_to_equations; lia | unfold USTACK_TOP; lia | exact RA4096 | apply bv_unsigned_in_range
                     | exact REC
                     | apply (chain_ok_keep ras m mc usp (bv_unsigned s0) UCTX); eapply agree_sub; [exact AGF|];
                       let xq := fresh "xq" in let Hxq := fresh "Hxq" in intros xq Hxq; cbv beta; split; [left; exact Hxq| cbn [outside]; split; [lia| exact I]] ] end
               | |- _ = [] -> _ => let HH := fresh "HH" in intros HH; discriminate HH
               | |- In _ CLIENT_TRACES => exact TRC
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- lres _ _ _ _ _ => lres_tac
               | |- ?g => idtac "LEFTOVER:" g
               end. }
        after_call RT AF.
        fold_ag ltac:(fun Hx => destruct Hx as [Hx1 _]; split; [apply (aclient_mono _ _ usp _ _ _ _ Hx1); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]| exact I]).
        lazymatch goal with H : rt_live RT _ = (if ?c =? 0 then _ else _) |- _ => rename H into LVH; set (cmapd := c) in * end.
        lazymatch goal with H : cmapd <> 0 -> cmap_obj _ _ _ ?c2 /\ _ |- _ => rename H into CMN; set (cvn := c2) in * end.
        hide CMN.
        destruct (Z.eq_dec cmapd 0) as [CZ|CNZ].
        -- (* [comment removed for export] *)
           clear CMN. rewrite CZ in *. change (0 =? 0) with true in LVH. cbv iota in LVH.
           refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. park_disj.
           walk_to AF MST [(usp - 96, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16); (pixd + 48, pixd + 56)] [0x8d86c; 0x8fcbc].
      at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac|
                           split; [intros zz Hzz; right; right; left; exists pixd, 64; split; [solve [in_live_tac]| lia]| exact I]]]])
                    ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; destruct Hx as [_ Hx2]; cbn [outside] in Hx2;
                                    unfold shad, SHB in *; repeat split; try exact I; first [tauto | lia | Z.div_mod_to_equations; lia]).
        eapply cps_seq.
        { eapply RE with (lo := lo); rt_side idtac.
          all: lazymatch goal with
               | |- exists l, In _ LEPT_LITS => rewrite ?unsigned_lit by lia; lit_in
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- (_ < _)%nat => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; cbn [length]; unfold FRAMES_MAX in *; lia
               | |- _ <= rt_credit _ _ => repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end; lia
               | |- ?g => idtac "LEFTOVER:" g
               end. }
        after_call RT AF.
        fold_ag ltac:(fun Hx => destruct Hx as [Hx1 _]; apply (aclient_mono _ _ usp _ _ _ _ Hx1); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| lia]).
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. park_disj.
        walk_to AF MST [(usp - 96, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16); (pixd + 48, pixd + 56)] [0x8fcbc].
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac|
                         split; [intros zz Hzz; right; right; left; exists pixd, 64; split; [solve [in_live_tac]| lia]| exact I]]]]).
    lazymatch goal with MUx : munch _ ?mm _ |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; destruct Hx as [_ Hx2]; cbn [outside] in Hx2;
                                         unfold shad, SHB in *; repeat split; try exact I; first [tauto | lia | Z.div_mod_to_equations; lia]) end.
    to_entry.
        eapply EPI with (cmapd := 0) (cv' := mkCmapv 0 0 0 0); try eassumption.
        all: lazymatch goal with
             | |- wr_at asegs _ _ 120 => first [eassumption | exact (proj2 FRM)]
             | |- wr_at asegs _ _ 16 => exact (proj2 FSH)
             | |- rw_cells asegs _ _ (pix_cells _) => unfold pix_cells, pixv_cmap; cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data]; exact PXDC
             | |- _ <= _ => repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end; lia
             | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
             | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
             | |- forall e, In e _ -> In e _ => solve [live_add_tac]
             | |- _ \/ _ => left; split; [reflexivity| repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity]
             | |- ?g => idtac "LEFTOVER:" g
             end.
        -- (* [comment removed for export] *)
           replace (cmapd =? 0) with false in LVH by (symmetry; apply Z.eqb_neq; exact CNZ).
           unfold hid in CMN. destruct (CMN CNZ) as (CMOn & EQD & EQNA & EQN). clear CMN.
           destruct CMOn as ((padn & CMCn) & (INCn & CN0 & CN16 & _) & (INAn & AN0 & AN16 & ANN) & CMOKn & NEQAn).
           unfold cmap_cells in CMCn.
           hide NEQAn. hide CNZ.
           lazymatch goal with A : ART RT ?S ?mc |- cps _ (ASTA RT ?S _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
             assert (INDn : In (pixd, 64) (rt_live RT S)) by (solve [in_live_tac]);
             assert (CDNE : cmapd <> pixd) by (apply (live_size_ne RT AF S mc cmapd 24 pixd 64 A INCn INDn); lia);
             pose proof (live_apart RT AF S mc cmapd 24 pixd 64 A INCn INDn CDNE) as CDD;
             (* [comment removed for export] *)
             assert (ADNE : c_arr cvn <> pixd)
               by (pose proof (live_head_apart RT AF S mc _ _ _ pixd 64 A LVH ltac:(right; solve [in_live_tac])) as Dq; clear - Dq ANN; lia);
             assert (DNEW : cmapd <> p_data vd /\ c_arr cvn <> p_data vd)
               by (unfold hid in DATD, PDATD; destruct DATD as [DZq|((DINq & _ & _ & DPq) & _)]; [contradiction|];
                   pose proof (live_head_apart RT AF S mc _ _ _ (p_data vd) (rsize vd) A LVH ltac:(right; solve [in_live_tac])) as Dq1;
                   pose proof (live_second_apart RT AF S mc _ _ _ _ _ (p_data vd) (rsize vd) A LVH ltac:(solve [in_live_tac])) as Dq2;
                   clear - Dq1 Dq2 DPq ANN; unfold rsize in *; lia)
           end.
           hide CDNE. hide ADNE. hide DNEW.
           chunk_facts RT AF GP cmapd 24.
           lazymatch goal with |- cps _ (ASTA RT ?S _ _) _ =>
             assert (FRSn : rt_frames RT S = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity) end.
           fframe_chunk RT AF fr 1%nat 128 cmapd 24.
           refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. park_disj.
           (* [comment removed for export] *)
           clear_acc.
           walk_to AF MST [(usp - 96, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16); (pixd + 48, pixd + 56)] [0x8faf4].
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac|
                         split; [intros zz Hzz; right; right; left; exists pixd, 64; split; [solve [in_live_tac]| lia]| exact I]]]]).
    lazymatch goal with MUx : munch _ ?mm _ |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; destruct Hx as [_ Hx2]; cbn [outside] in Hx2;
                                         unfold shad, SHB in *; repeat split; try exact I; first [tauto | lia | Z.div_mod_to_equations; lia]) end.
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *.
           walk_to AF MST [(usp - 96, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16); (pixd + 48, pixd + 56)] [0x8fb20].
           clear_acc.
           cwalk [0x8fb24].
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac|
                         split; [intros zz Hzz; right; right; left; exists pixd, 64; split; [solve [in_live_tac]| lia]| exact I]]]]).
    lazymatch goal with MUx : munch _ ?mm _ |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; destruct Hx as [_ Hx2]; cbn [outside] in Hx2;
                                         unfold shad, SHB in *; repeat split; try exact I; first [tauto | lia | Z.div_mod_to_equations; lia]) end.
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *.
           walk_to AF MST [(usp - 96, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16); (pixd + 48, pixd + 56)] [0x8fb28].
           lstep. shbr8z.
           cwalk [0x91944; 0x8d86c; 0x8fcbc].
           (* [comment removed for export] *)
           split_at FRM 5%nat FRt. split_at FRt 1%nat FRtail. split_last_CB FRt [24; 4; 12]%nat.
           split_at FRt 1%nat FRv2. split_at FRv2 1%nat FRv2r.
           destruct (cb4_c4 _ _ _ FRv2) as (v2 & VC2). clear FRv2.
           pose proof FSH as T1; split_at T1 8%nat SHV2; split_at SHV2 1%nat T3; clear T1 T3.
      at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac|
                           split; [intros zz Hzz; right; right; left; exists pixd, 64; split; [solve [in_live_tac]| lia]| exact I]]]])
                    ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; destruct Hx as [_ Hx2]; cbn [outside] in Hx2;
                                    unfold shad, SHB in *; repeat split; try exact I; first [tauto | lia | Z.div_mod_to_equations; lia]).
           eapply cps_seq.
           { eapply VLD with (lo := lo) (cmap := cmapd) (pix := 0) (pv := fr + 64) (cv := cvn) (v := mkPixv 0 0 0 0 0 0 0 0 0 0 0) (x := v2); rt_side idtac.
             all: lazymatch goal with
                  | |- cmap_obj _ _ _ _ =>
                      unfold cmap_obj, cmap_cells, chunk;
                      split; [eexists; exact CMCn|]; split; [split; [solve [in_live_tac]| split; [assumption| split; [assumption| lia]]]|];
                      split; [split; [solve [in_live_tac]| split; [assumption| split; [assumption| assumption]]]|]; split; [exact CMOKn| unfold hid in NEQAn; exact NEQAn]
                  | |- _ \/ _ => left; reflexivity
                  | |- optrF _ _ _ _ _ =>
                      unfold optrF, own_frame; unfold parked in *; split;
                      [ exists fr, 1%nat; change (fs_size 1) with 128;
                        split; [solve [frames_in_tac]|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
                        split; [lia|]; split; [ul|];
                        lazymatch type of SHV2 with rw_cells _ _ ?A _ => replace (shad (fr + 64)) with A by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia) end;
                        destruct SHV2 as [[_ B] _]; exact B
                      | split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|]; split; [lia| right; ul] ]
                  | |- rw_cells _ _ _ [C4 _] => exact VC2
                  | |- lenv _ _ _ _ _ _ => lenv_tac
                  | |- lres _ _ _ _ _ => lres_tac
                  | |- ?g => idtac "LEFTOVER:" g
                  end. }
           after_call RT AF.
           fold_ag ltac:(fun Hx => pose proof (NFA _ Hx) as [N1 _]; destruct Hx as [Hx1 _];
                         first [ split; [apply (aclient_mono _ _ usp _ _ _ _ Hx1); [solve [live_add_tac]| solve [frames_sub_tac]| lia]
                                        | cbn [outside]; split; [lia| exact I]]
                               | apply (aclient_mono _ _ usp _ _ _ _ Hx1); [solve [live_add_tac]| solve [frames_sub_tac]| lia] ]).
           refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. park_disj.
           lazymatch goal with H : rw_cells asegs _ (fr + 64) [C4 _] |- _ => rename H into VC3 end.
           walk_to AF MST [(usp - 96, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16); (pixd + 48, pixd + 56)] [0x8d86c; 0x8fcbc].
           clear SHV2. try clear SHV.
           if_cases HV2; clear HV2.
           ++ (* [comment removed for export] *)
              cwalk [0x8fcbc].
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac|
                         split; [intros zz Hzz; right; right; left; exists pixd, 64; split; [solve [in_live_tac]| lia]| exact I]]]]).
    lazymatch goal with MUx : munch _ ?mm _ |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; destruct Hx as [_ Hx2]; cbn [outside] in Hx2;
                                         unfold shad, SHB in *; repeat split; try exact I; first [tauto | lia | Z.div_mod_to_equations; lia]) end.
    to_entry.
              eapply EPI with (cmapd := cmapd) (cv' := cvn); try eassumption.
              all: lazymatch goal with
                   | |- wr_at asegs _ _ 120 => eassumption
                   | |- wr_at asegs _ _ 16 => exact (proj2 FSH)
                   | |- rw_cells asegs _ _ (pix_cells _) => unfold pix_cells, pixv_cmap; cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data]; exact PXDC
                   | |- _ <= _ => repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end; lia
                   | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
                   | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
                   | |- forall e, In e _ -> In e _ => solve [live_add_tac]
                   | |- _ \/ _ =>
                       right; unfold hid in CNZ, CDNE, ADNE, DNEW, PCNZ, NEQAn; destruct DNEW as [DN1 DN2];
                       split; [exact CNZ|]; split;
                       [ unfold cmap_obj, cmap_cells, chunk;
                         split; [eexists; exact CMCn|]; split; [split; [solve [in_live_tac]| split; [assumption| split; [assumption| lia]]]|];
                         split; [split; [solve [in_live_tac]| split; [assumption| split; [assumption| assumption]]]|]; split; [exact CMOKn| exact NEQAn] |];
                       split; [exact CDNE|]; split; [exact ADNE|]; split; [exact DN1|]; split; [exact DN2|]; split; [exact PCNZ|];
                       split; [exact EQD|]; split; [exact EQNA|]; split; [exact EQN|];
                       repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity
                   | |- ?g => idtac "LEFTOVER:" g
                   end.
           ++ (* [comment removed for export] *)
              cwalk [0x8d86c; 0x8fcbc].
      at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac|
                           split; [intros zz Hzz; right; right; left; exists pixd, 64; split; [solve [in_live_tac]| lia]| exact I]]]])
                    ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; destruct Hx as [_ Hx2]; cbn [outside] in Hx2;
                                    unfold shad, SHB in *; repeat split; try exact I; first [tauto | lia | Z.div_mod_to_equations; lia]).
        eapply cps_seq.
        { eapply RE with (lo := lo); rt_side idtac.
          all: lazymatch goal with
               | |- exists l, In _ LEPT_LITS => rewrite ?unsigned_lit by lia; lit_in
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- (_ < _)%nat => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; cbn [length]; unfold FRAMES_MAX in *; lia
               | |- _ <= rt_credit _ _ => repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end; lia
               | |- ?g => idtac "LEFTOVER:" g
               end. }
        after_call RT AF.
        fold_ag ltac:(fun Hx => destruct Hx as [Hx1 _]; apply (aclient_mono _ _ usp _ _ _ _ Hx1); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| lia]).
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. park_disj.
        walk_to AF MST [(usp - 96, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16); (pixd + 48, pixd + 56)] [0x8fcbc].
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac|
                         split; [intros zz Hzz; right; right; left; exists pixd, 64; split; [solve [in_live_tac]| lia]| exact I]]]]).
    lazymatch goal with MUx : munch _ ?mm _ |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; destruct Hx as [_ Hx2]; cbn [outside] in Hx2;
                                         unfold shad, SHB in *; repeat split; try exact I; first [tauto | lia | Z.div_mod_to_equations; lia]) end.
    to_entry.
              eapply EPI with (cmapd := cmapd) (cv' := cvn); try eassumption.
              all: lazymatch goal with
                   | |- wr_at asegs _ _ 120 => eassumption
                   | |- wr_at asegs _ _ 16 => exact (proj2 FSH)
                   | |- rw_cells asegs _ _ (pix_cells _) => unfold pix_cells, pixv_cmap; cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data]; exact PXDC
                   | |- _ <= _ => repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end; lia
                   | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
                   | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
                   | |- forall e, In e _ -> In e _ => solve [live_add_tac]
                   | |- _ \/ _ =>
                       right; unfold hid in CNZ, CDNE, ADNE, DNEW, PCNZ, NEQAn; destruct DNEW as [DN1 DN2];
                       split; [exact CNZ|]; split;
                       [ unfold cmap_obj, cmap_cells, chunk;
                         split; [eexists; exact CMCn|]; split; [split; [solve [in_live_tac]| split; [assumption| split; [assumption| lia]]]|];
                         split; [split; [solve [in_live_tac]| split; [assumption| split; [assumption| assumption]]]|]; split; [exact CMOKn| exact NEQAn] |];
                       split; [exact CDNE|]; split; [exact ADNE|]; split; [exact DN1|]; split; [exact DN2|]; split; [exact PCNZ|];
                       split; [exact EQD|]; split; [exact EQNA|]; split; [exact EQN|];
                       repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity
                   | |- ?g => idtac "LEFTOVER:" g
                   end.
  - (* [comment removed for export] *)
    carve_frame 112%nat ST.
    clear_acc.
    walk_to AF MST [(usp - 112, usp)] [0x4896c].
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                  ltac:(fun Hx => cbn [outside]; split; [destruct (PFS _ Hx); lia| exact I]).
    eapply cps_seq.
    { eapply (gp_stack_malloc_1 RT GP) with (lo := lo); rt_side idtac. }
    after_call RT AF.
    fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [auto| auto| lia]).
    fframe_open RT AF PF (rt_live RT Σ) usp 1%nat 128 ltac:(fun Ha => exact (proj1 Ha)).
    fframe_chunk RT AF fr 1%nat 128 pixd 64.
    fframe_chunk RT AF fr 1%nat 128 pixs 64.
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. clear_acc. park_disj.
    walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x8fa24].
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
    lazymatch goal with MUx : munch _ ?mm _ |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                         repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *.
    (* [comment removed for export] *)
    lazymatch goal with FRx : rw_cells asegs _ (usp + -112) ?cs |- _ =>
      assert (EPI : forall (S : rts RT) (mE : mem) (rv : word) (cmapd : Z) (cv' : cmapv)
                (r1 r5 r6 r7 r9 r11 r12 r13 r14 r15 r16 r17 r19 r20 r21 r24 r25 r28 r29 r30 r31 : word) F' fc',
          ART RT S mE -> mem_inv asegs mE -> stk asegs mE lo (usp + -112) -> rw_cells asegs mE (usp + -112) cs ->
          wr_at asegs mE fr 120 -> wr_at asegs mE (fr / 8 + 2147450880) 16 ->
          LIBH mE -> io_ssp mE -> agree_on PF m mE -> wmono asegs m mE ->
          rt_frames RT S = (fr, 1%nat) :: rt_frames RT Σ -> rt_sp0 RT S = rt_sp0 RT Σ -> rt_credit RT Σ - 16 <= rt_credit RT S ->
          (forall e, In e (rt_live RT Σ) -> In e (rt_live RT S)) ->
          rw_cells asegs mE pixd (pix_cells (pixv_cmap vd cmapd)) ->
          ((cmapd = 0 /\ rt_live RT S = rt_live RT Σ)
           \/ (cmapd <> 0 /\ cmap_obj (rt_live RT S) mE cmapd cv'
               /\ cmapd <> pixd /\ c_arr cv' <> pixd /\ cmapd <> p_data vd /\ c_arr cv' <> p_data vd
               /\ p_cmap v <> 0 /\ c_depth cv' = c_depth cv /\ c_nalloc cv' = c_nalloc cv /\ c_n cv' = c_n cv
               /\ rt_live RT S = (c_arr cv', 4 * c_nalloc cv') :: (cmapd, 24) :: rt_live RT Σ)) ->
          cps asegs (ASTA RT S PMc (eq (entry_st r1 (Z_to_bv 64 (usp + -112)) gp (Z_to_bv 64 TP_A) r5 r6 r7 (Z_to_bv 64 usp) r9
                                          rv r11 r12 r13 r14 r15 r16 r17 (Z_to_bv 64 fr) r19 r20 r21 (Z_to_bv 64 (fr / 8 + 2147450880))
                                          (Z_to_bv 64 fr) r24 r25 s10 s11 r28 r29 r30 r31 F' fc' 0x8fcbc mE))) QF) end.
    { intros S mE rv cmapd cv' r1 r5 r6 r7 r9 r11 r12 r13 r14 r15 r16 r17 r19 r20 r21 r24 r25 r28 r29 r30 r31 F' fc'
        ARTE MIE STE FRE WFE WSE LHE SSPE AGE WME EFR ESP0 ECR LSUB PXE PAY.
      clear AGF. rename AGE into AGF.
      repeat match goal with H : rw_cells asegs _ _ _ |- _ => lazymatch H with FRE => fail | PXE => fail | _ => clear H end end.
      repeat match goal with H : ro_cells asegs _ _ _ |- _ => clear H end.
      repeat match goal with H : ART RT _ _ |- _ => lazymatch H with ARTE => fail | _ => clear H end end.
      repeat match goal with H : LIBH _ |- _ => lazymatch H with LHE => fail | _ => clear H end end.
      repeat match goal with H : io_ssp _ |- _ => lazymatch H with SSPE => fail | _ => clear H end end.
      repeat match goal with H : stk asegs _ _ _ |- _ => lazymatch H with STE => fail | _ => clear H end end.
      repeat match goal with H : mem_inv asegs _ |- _ => lazymatch H with MIE => fail | _ => clear H end end.
      repeat match goal with H : wmono asegs _ _ |- _ => lazymatch H with WME => fail | _ => clear H end end.
      repeat match goal with H : munch _ _ _ |- _ => clear H end.
      repeat match goal with H : rt_frames RT _ = _ |- _ => lazymatch H with EFR => fail | _ => clear H end end.
      repeat match goal with H : rt_live RT _ = _ |- _ => clear H end.
      repeat match goal with H : rt_sp0 RT _ = _ |- _ => lazymatch H with ESP0 => fail | _ => clear H end end.
      repeat match goal with H : rt_credit RT _ = _ |- _ => clear H end.
      clear_acc.
      destruct (wr_at_rw_CB mE fr 120 WFE ltac:(lia)) as (jfE & FRME). destruct (wr_at_rw_CB mE (fr / 8 + 2147450880) 16 WSE ltac:(lia)) as (jsE & FSHE).
      change (Z.to_nat 120) with 120%nat in FRME. change (Z.to_nat 16) with 16%nat in FSHE.
      (* [comment removed for export] *)
      assert (LOUT : forall b k, In (b, k) (rt_live RT S) -> forall x, b <= x < b + k ->
                outside [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] x).
      { intros bb kk Hb zz Hz.
        pose proof (af_live_range RT AF S mE bb kk ARTE Hb) as LR.
        pose proof (af_frames_range RT AF S mE fr 1%nat ARTE ltac:(rewrite EFR; left; reflexivity)) as (_ & _ & _ & D1). specialize (D1 bb kk Hb).
        pose proof (af_fshadow_apart RT AF S mE fr 1%nat ARTE ltac:(rewrite EFR; left; reflexivity)) as (D2 & _). specialize (D2 bb kk Hb).
        change (fs_size 1) with 128 in D1, D2. unfold shad, SHB in D2. rewrite ESP0 in LR. unfold STACK_WIN in LR.
        cbn [outside]. clear - LR D1 D2 Hz LOW LOR. repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]. }
      hide PAY. hide LOUT. hide LSUB.
      hide PXE. (* [comment removed for export] *)
      unfold entry_st.
      walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x8fd18].
      lazymatch goal with MUx : munch _ mE ?mc |- _ =>
        assert (KEEP1 : keeps_live (rt_live RT S) mE mc)
          by (unfold hid in LOUT; let bb := fresh "bb" in let kk := fresh "kk" in let Hb := fresh "Hb" in let a := fresh "a" in let Ha := fresh "Ha" in
              intros bb kk Hb a Ha; apply MUx; exact (LOUT bb kk Hb _ Ha)) end.
      frame_release RT AF GP MST Σ fr 1%nat 128 PF AGF PFS usp lo 0x8fd20
        ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
        ltac:(fun Hx => let N1 := fresh "N1" in let N2 := fresh "N2" in
                        cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                        repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
      walk_to AF MST [(usp - 112, usp)] (@nil Z).
    lazymatch goal with ST' : stk asegs _ lo (usp + -112), FR' : rw_cells asegs _ (usp + -112) _ |- _ => release_frame FR' ST' usp end.
      cps_stop.
      try (lazymatch goal with STx : stk asegs _ lo (usp + -112) |- _ => release_frame FRE STx usp end).
      art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I]).
      lazymatch goal with MUx : munch _ ?mm ?mc |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
        assert (KEEP3 : keeps_live (rt_live RT S) mm mc)
          by (unfold hid in LOUT; let bb := fresh "bb" in let kk := fresh "kk" in let Hb := fresh "Hb" in let a := fresh "a" in let Ha := fresh "Ha" in
              intros bb kk Hb a Ha; apply MUx; cbn [outside]; split; [exact (proj1 (LOUT bb kk Hb _ Ha))| exact I]);
        agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]) end.
      lazymatch goal with K3 : keeps_live _ _ ?mc |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
        assert (KEEPF : keeps_live (rt_live RT S) mE mc)
          by (eapply keeps_live_trans; [exact KEEP1|]; eapply keeps_live_trans; [exact KEEPR| exact K3]) end.
      unfold hid in LSUB, PAY, DATD, HOKD, PXE.
      assert (PINS : In (pixd, 64) (rt_live RT S)) by (exact (LSUB _ IND)).
      apply cps_finish. intros c0 Hc. subst QF. cbv beta.
      lazymatch type of Hc with ASTA RT ?S' _ _ _ => exists S', rv, cmapd, cv' end.
      split.
      { eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-. eexists.
        split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
        split; [split; [split; [assumption| split; [assumption| split; [| assumption]]]| split; assumption]|].
        { lazymatch goal with WMx : wmono asegs m ?mf |- wmono asegs m ?mf => exact WMx end. }
        split; [intros xa HXa HXo; apply AGF; split; [exact HXa| exact HXo]|].
        split.
        - (* [comment removed for export] *)
          rewrite LV2. unfold pix_obj.
          split; [apply (keeps_live_cells (rt_live RT S) mE _ pixd 64 pixd _ KEEPF PINS); [lia| cbn; lia| exact PXE]|].
          split; [split; [exact PINS| split; [exact PD0| split; [exact PD16| lia]]]|].
          split; [exact HOKD|].
          split.
          + cbn [p_data pixv_cmap]. destruct DATD as [DZ|((DIN & DR) & DNE)]; [left; exact DZ| right].
            split; [split; [exact (LSUB _ DIN)| exact DR]| exact DNE].
          + cbn [p_cmap p_data pixv_cmap]. destruct PAY as [(E0 & _)|(NE0 & CMO & N1 & N2 & N3 & N4 & _)]; [left; exact E0| right].
            split; [exact (cmap_obj_keep _ mE _ cmapd cv' KEEPF CMO)|]. repeat split; assumption.
        - intros NE0. destruct PAY as [(E0 & _)|(_ & _ & _ & _ & _ & _ & PCN & E1 & E2 & E3 & _)]; [contradiction|]. repeat split; assumption. }
      rewrite LV2, FRS2, SP2, CR2.
      split; [| split; [reflexivity| split; [exact ESP0| lia]]].
      destruct PAY as [(E0 & EL)|(NE0 & PAYR)].
      - rewrite E0. change (0 =? 0) with true. cbv iota. exact EL.
      - replace (cmapd =? 0) with false by (symmetry; apply Z.eqb_neq; exact NE0).
        destruct PAYR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & EL). exact EL. }

    assert (DRS : 1 <= p_d v <= 32) by (unfold hid in HOKS; destruct HOKS as (HDP & _); clear - HDP; cbn [In] in HDP; lia).
    pose proof NEQ as NEQ1. unfold hid in NEQ1.
    walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16); (pixd + 48, pixd + 56)] [0x8fa64].
    cwalk [0x8fa64].
    clear NEQ1. clear_acc.
    cwalk [0x8fa68].
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac|
                         split; [intros zz Hzz; right; right; left; exists pixd, 64; split; [solve [in_live_tac]| lia]| exact I]]]]).
    lazymatch goal with MUx : munch _ ?mm _ |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; destruct Hx as [_ Hx2]; cbn [outside] in Hx2;
                                         unfold shad, SHB in *; repeat split; try exact I; first [tauto | lia | Z.div_mod_to_equations; lia]) end.
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *.
    walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16); (pixd + 48, pixd + 56)] [0x8faa4].
    clear_acc.
    cwalk [0x8faa8].
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac|
                         split; [intros zz Hzz; right; right; left; exists pixd, 64; split; [solve [in_live_tac]| lia]| exact I]]]]).
    lazymatch goal with MUx : munch _ ?mm _ |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; destruct Hx as [_ Hx2]; cbn [outside] in Hx2;
                                         unfold shad, SHB in *; repeat split; try exact I; first [tauto | lia | Z.div_mod_to_equations; lia]) end.
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *.
    walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16); (pixd + 48, pixd + 56)] [0x91944; 0x8fcbc].
    unfold hid in PCMS. destruct PCMS as [PCZ | (CMO & NC1 & NC2 & NC3 & NC4)].
    + (* [comment removed for export] *)
      rewrite PCZ in *.
      brT. cwalk [0x8fcbc].
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac|
                         split; [intros zz Hzz; right; right; left; exists pixd, 64; split; [solve [in_live_tac]| lia]| exact I]]]]).
    lazymatch goal with MUx : munch _ ?mm _ |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; destruct Hx as [_ Hx2]; cbn [outside] in Hx2;
                                         unfold shad, SHB in *; repeat split; try exact I; first [tauto | lia | Z.div_mod_to_equations; lia]) end.
    to_entry.
        eapply EPI with (cmapd := 0) (cv' := mkCmapv 0 0 0 0); try eassumption.
        all: lazymatch goal with
             | |- wr_at asegs _ _ 120 => first [eassumption | exact (proj2 FRM)]
             | |- wr_at asegs _ _ 16 => exact (proj2 FSH)
             | |- rw_cells asegs _ _ (pix_cells _) => unfold pix_cells, pixv_cmap; cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data]; exact PXDC
             | |- _ <= _ => repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end; lia
             | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
             | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
             | |- forall e, In e _ -> In e _ => solve [live_add_tac]
             | |- _ \/ _ => left; split; [reflexivity| repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity]
             | |- ?g => idtac "LEFTOVER:" g
             end.
    + (* [comment removed for export] *)
      clear NC1 NC2 NC3 NC4.
      pose proof CMO as ((pad & CMC) & (INC & CM0 & CM16 & _) & (INA & AR0 & AR16 & ARN) & CMOK & NEQA). clear pad CMC. hide NEQA.
      assert (CMNE : p_cmap v <> pixd) by (apply (live_size_ne RT AF Σ m (p_cmap v) 24 pixd 64 ART0 INC IND); lia).
      pose proof (live_apart RT AF Σ m (p_cmap v) 24 pixd 64 ART0 INC IND CMNE) as CMD. clear CMNE.
      (* [comment removed for export] *)
      assert (KCM : forall mc, agree_on PF m mc -> keeps_live [(p_cmap v, 24)] m mc).
      { intros mc AG. apply (keeps_live_of_agree (rt_live RT Σ) (rt_frames RT Σ) usp [(pixd + 48, pixd + 56)] m mc _ AG).
        - intros e [<-|[]]. exact INC.
        - intros bq kq zq [Eq|[]] Hzq. injection Eq as <- <-. cbn [outside]. split; [| exact I]. clear - CMD Hzq. lia. }
      park CMD.
      assert (PCNZ : p_cmap v <> 0) by lia.
      chunk_facts RT AF GP (p_cmap v) 24. park_disj.
      brF. hide PCNZ.
      cwalk [0x91944; 0x8fcbc].
      (* [comment removed for export] *)
      split_last_CB FRM [24; 4; 4]%nat. split_at FRM 6%nat FRv. split_at FRv 1%nat FRrest.
      destruct (cb4_c4 _ _ _ FRv) as (v0 & VC0). clear FRv.
      pose proof FSH as T1; split_at T1 14%nat SHV; split_at SHV 1%nat T3; clear T1 T3.
      at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac|
                           split; [intros zz Hzz; right; right; left; exists pixd, 64; split; [solve [in_live_tac]| lia]| exact I]]]])
                    ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; destruct Hx as [_ Hx2]; cbn [outside] in Hx2;
                                    unfold shad, SHB in *; repeat split; try exact I; first [tauto | lia | Z.div_mod_to_equations; lia]).
      lazymatch goal with AGx : agree_on PF m ?mc |- _ => pose proof (cmap_obj_keep1 _ m mc _ cv (KCM mc AGx) CMO) as CMOc end.
      eapply cps_seq.
      { eapply VLD with (lo := lo) (cmap := p_cmap v) (pix := 0) (pv := fr + 112) (cv := cv) (v := mkPixv 0 0 0 0 0 0 0 0 0 0 0) (x := v0); rt_side idtac.
        all: lazymatch goal with
             | |- cmap_obj _ _ _ _ => repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact CMOc
             | |- _ \/ _ => left; reflexivity
             | |- optrF _ _ _ _ _ =>
                 unfold optrF, own_frame; unfold parked in *; split;
                 [ exists fr, 1%nat; change (fs_size 1) with 128;
                   split; [solve [frames_in_tac]|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
                   split; [lia|]; split; [ul|];
                   lazymatch type of SHV with rw_cells _ _ ?A _ => replace (shad (fr + 112)) with A by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia) end;
                   destruct SHV as [[_ B] _]; exact B
                 | split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|]; split; [lia| right; ul] ]
             | |- rw_cells _ _ _ [C4 _] => exact VC0
             | |- lenv _ _ _ _ _ _ => lenv_tac
             | |- lres _ _ _ _ _ => lres_tac
             | |- ?g => idtac "LEFTOVER:" g
             end. }
      after_call RT AF.
      fold_ag ltac:(fun Hx => pose proof (NFA _ Hx) as [N1 _]; destruct Hx as [Hx1 _];
                    first [ split; [apply (aclient_mono _ _ usp _ _ _ _ Hx1); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]
                                   | cbn [outside]; split; [lia| exact I]]
                          | apply (aclient_mono _ _ usp _ _ _ _ Hx1); [solve [live_sub_tac]| solve [frames_sub_tac]| lia] ]).
      refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. park_disj.
      lazymatch goal with H : rw_cells asegs _ (fr + 112) [C4 _] |- _ => rename H into VC1 end.
      (* [comment removed for export] *)
      lazymatch goal with F1 : rw_cells asegs ?mm fr _, F2 : rw_cells asegs ?mm (fr + 112) [C4 _], F3 : rw_cells asegs ?mm (fr + 116) _ |- _ =>
        assert (WF120 : wr_at asegs mm fr 120)
          by (apply (proj2 (wr_at_app mm fr 112 8 ltac:(lia) ltac:(lia))); split; [exact (proj2 F1)|];
              apply (proj2 (wr_at_app mm (fr + 112) 4 4 ltac:(lia) ltac:(lia))); split; [exact (proj2 F2)|];
              replace (fr + 112 + 4) with (fr + 116) by lia; exact (proj2 F3)) end.
      walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16); (pixd + 48, pixd + 56)] [0x91680; 0x8d86c; 0x8fcbc].
      if_cases HV; clear HV.
      * (* [comment removed for export] *)
        cwalk [0x8d86c; 0x8fcbc].
      at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac|
                           split; [intros zz Hzz; right; right; left; exists pixd, 64; split; [solve [in_live_tac]| lia]| exact I]]]])
                    ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; destruct Hx as [_ Hx2]; cbn [outside] in Hx2;
                                    unfold shad, SHB in *; repeat split; try exact I; first [tauto | lia | Z.div_mod_to_equations; lia]).
        eapply cps_seq.
        { eapply RE with (lo := lo); rt_side idtac.
          all: lazymatch goal with
               | |- exists l, In _ LEPT_LITS => rewrite ?unsigned_lit by lia; lit_in
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- (_ < _)%nat => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; cbn [length]; unfold FRAMES_MAX in *; lia
               | |- _ <= rt_credit _ _ => repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end; lia
               | |- ?g => idtac "LEFTOVER:" g
               end. }
        after_call RT AF.
        fold_ag ltac:(fun Hx => destruct Hx as [Hx1 _]; apply (aclient_mono _ _ usp _ _ _ _ Hx1); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| lia]).
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. park_disj.
        walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16); (pixd + 48, pixd + 56)] [0x8fcbc].
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac|
                         split; [intros zz Hzz; right; right; left; exists pixd, 64; split; [solve [in_live_tac]| lia]| exact I]]]]).
    lazymatch goal with MUx : munch _ ?mm _ |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; destruct Hx as [_ Hx2]; cbn [outside] in Hx2;
                                         unfold shad, SHB in *; repeat split; try exact I; first [tauto | lia | Z.div_mod_to_equations; lia]) end.
    to_entry.
        eapply EPI with (cmapd := 0) (cv' := mkCmapv 0 0 0 0); try eassumption.
        all: lazymatch goal with
             | |- wr_at asegs _ _ 120 => first [eassumption | exact (proj2 FRM)]
             | |- wr_at asegs _ _ 16 => exact (proj2 FSH)
             | |- rw_cells asegs _ _ (pix_cells _) => unfold pix_cells, pixv_cmap; cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data]; exact PXDC
             | |- _ <= _ => repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end; lia
             | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
             | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
             | |- forall e, In e _ -> In e _ => solve [live_add_tac]
             | |- _ \/ _ => left; split; [reflexivity| repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity]
             | |- ?g => idtac "LEFTOVER:" g
             end.
      * (* [comment removed for export] *)
        cwalk [0x91680; 0x8d86c; 0x8fcbc].
        assert (RA4096 : 4096 <= bv_unsigned ra < 2^64).
        { pose proof client_traces_wf as Wq. rewrite forallb_forall in Wq. specialize (Wq _ TRC).
          apply andb_prop in Wq. destruct Wq as [_ Wq]. cbn [forallb] in Wq.
          apply andb_prop in Wq. destruct Wq as [_ Wq]. apply andb_prop in Wq. destruct Wq as [Wq _].
          apply andb_prop in Wq. destruct Wq as [Wq _]. apply andb_prop in Wq. destruct Wq as [Wq1 Wq2].
          apply Z.leb_le in Wq1. apply Z.ltb_lt in Wq2. lia. }
      at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac|
                           split; [intros zz Hzz; right; right; left; exists pixd, 64; split; [solve [in_live_tac]| lia]| exact I]]]])
                    ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; destruct Hx as [_ Hx2]; cbn [outside] in Hx2;
                                    unfold shad, SHB in *; repeat split; try exact I; first [tauto | lia | Z.div_mod_to_equations; lia]).
        lazymatch goal with AGx : agree_on PF m ?mc |- _ => pose proof (cmap_obj_keep1 _ m mc _ cv (KCM mc AGx) CMO) as CMOd end.
        eapply cps_seq.
        { eapply CPY with (lo := lo) (cmaps := p_cmap v) (cv := cv) (ras := bv_unsigned ra :: ras); rt_side idtac.
          all: lazymatch goal with
               | |- cmap_obj _ _ _ _ => repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact CMOd
               | |- uctx _ _ _ _ =>
                   unfold uctx; rewrite ?unsigned_lit by lia;
                   lazymatch goal with |- chain_ok ?mc _ _ _ =>
                     let FRc := fresh "FRc" in let REC := fresh "REC" in
                     pose proof FR as FRc; split_before FRc (C8 s0) REC; clear FRc;
                     replace (C8 s0) with (C8 (Z_to_bv 64 (bv_unsigned s0))) in REC by (rewrite Z_to_bv_bv_unsigned; reflexivity);
                     replace (C8 ra) with (C8 (Z_to_bv 64 (bv_unsigned ra))) in REC by (rewrite Z_to_bv_bv_unsigned; reflexivity);
                     apply (chain_ok_push mc _ usp (bv_unsigned ra) (bv_unsigned s0) ras);
                     [ lia | clear - SPA; Z.div_mod_to_equations; lia | unfold USTACK_TOP; lia | exact RA4096 | apply bv_unsigned_in_range
                     | exact REC
                     | apply (chain_ok_keep ras m mc usp (bv_unsigned s0) UCTX); eapply agree_sub; [exact AGF|];
                       let xq := fresh "xq" in let Hxq := fresh "Hxq" in intros xq Hxq; cbv beta; split; [left; exact Hxq| cbn [outside]; split; [lia| exact I]] ] end
               | |- _ = [] -> _ => let HH := fresh "HH" in intros HH; discriminate HH
               | |- In _ CLIENT_TRACES => exact TRC
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- lres _ _ _ _ _ => lres_tac
               | |- ?g => idtac "LEFTOVER:" g
               end. }
        after_call RT AF.
        fold_ag ltac:(fun Hx => destruct Hx as [Hx1 _]; split; [apply (aclient_mono _ _ usp _ _ _ _ Hx1); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]| exact I]).
        lazymatch goal with H : rt_live RT _ = (if ?c =? 0 then _ else _) |- _ => rename H into LVH; set (cmapd := c) in * end.
        lazymatch goal with H : cmapd <> 0 -> cmap_obj _ _ _ ?c2 /\ _ |- _ => rename H into CMN; set (cvn := c2) in * end.
        hide CMN.
        destruct (Z.eq_dec cmapd 0) as [CZ|CNZ].
        -- (* [comment removed for export] *)
           clear CMN. rewrite CZ in *. change (0 =? 0) with true in LVH. cbv iota in LVH.
           refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. park_disj.
           walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16); (pixd + 48, pixd + 56)] [0x8d86c; 0x8fcbc].
      at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac|
                           split; [intros zz Hzz; right; right; left; exists pixd, 64; split; [solve [in_live_tac]| lia]| exact I]]]])
                    ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; destruct Hx as [_ Hx2]; cbn [outside] in Hx2;
                                    unfold shad, SHB in *; repeat split; try exact I; first [tauto | lia | Z.div_mod_to_equations; lia]).
        eapply cps_seq.
        { eapply RE with (lo := lo); rt_side idtac.
          all: lazymatch goal with
               | |- exists l, In _ LEPT_LITS => rewrite ?unsigned_lit by lia; lit_in
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- (_ < _)%nat => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; cbn [length]; unfold FRAMES_MAX in *; lia
               | |- _ <= rt_credit _ _ => repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end; lia
               | |- ?g => idtac "LEFTOVER:" g
               end. }
        after_call RT AF.
        fold_ag ltac:(fun Hx => destruct Hx as [Hx1 _]; apply (aclient_mono _ _ usp _ _ _ _ Hx1); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| lia]).
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. park_disj.
        walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16); (pixd + 48, pixd + 56)] [0x8fcbc].
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac|
                         split; [intros zz Hzz; right; right; left; exists pixd, 64; split; [solve [in_live_tac]| lia]| exact I]]]]).
    lazymatch goal with MUx : munch _ ?mm _ |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; destruct Hx as [_ Hx2]; cbn [outside] in Hx2;
                                         unfold shad, SHB in *; repeat split; try exact I; first [tauto | lia | Z.div_mod_to_equations; lia]) end.
    to_entry.
        eapply EPI with (cmapd := 0) (cv' := mkCmapv 0 0 0 0); try eassumption.
        all: lazymatch goal with
             | |- wr_at asegs _ _ 120 => first [eassumption | exact (proj2 FRM)]
             | |- wr_at asegs _ _ 16 => exact (proj2 FSH)
             | |- rw_cells asegs _ _ (pix_cells _) => unfold pix_cells, pixv_cmap; cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data]; exact PXDC
             | |- _ <= _ => repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end; lia
             | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
             | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
             | |- forall e, In e _ -> In e _ => solve [live_add_tac]
             | |- _ \/ _ => left; split; [reflexivity| repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity]
             | |- ?g => idtac "LEFTOVER:" g
             end.
        -- (* [comment removed for export] *)
           replace (cmapd =? 0) with false in LVH by (symmetry; apply Z.eqb_neq; exact CNZ).
           unfold hid in CMN. destruct (CMN CNZ) as (CMOn & EQD & EQNA & EQN). clear CMN.
           destruct CMOn as ((padn & CMCn) & (INCn & CN0 & CN16 & _) & (INAn & AN0 & AN16 & ANN) & CMOKn & NEQAn).
           unfold cmap_cells in CMCn.
           hide NEQAn. hide CNZ.
           lazymatch goal with A : ART RT ?S ?mc |- cps _ (ASTA RT ?S _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
             assert (INDn : In (pixd, 64) (rt_live RT S)) by (solve [in_live_tac]);
             assert (CDNE : cmapd <> pixd) by (apply (live_size_ne RT AF S mc cmapd 24 pixd 64 A INCn INDn); lia);
             pose proof (live_apart RT AF S mc cmapd 24 pixd 64 A INCn INDn CDNE) as CDD;
             (* [comment removed for export] *)
             assert (ADNE : c_arr cvn <> pixd)
               by (pose proof (live_head_apart RT AF S mc _ _ _ pixd 64 A LVH ltac:(right; solve [in_live_tac])) as Dq; clear - Dq ANN; lia);
             assert (DNEW : cmapd <> p_data vd /\ c_arr cvn <> p_data vd)
               by (unfold hid in DATD, PDATD; destruct DATD as [DZq|((DINq & _ & _ & DPq) & _)]; [contradiction|];
                   pose proof (live_head_apart RT AF S mc _ _ _ (p_data vd) (rsize vd) A LVH ltac:(right; solve [in_live_tac])) as Dq1;
                   pose proof (live_second_apart RT AF S mc _ _ _ _ _ (p_data vd) (rsize vd) A LVH ltac:(solve [in_live_tac])) as Dq2;
                   clear - Dq1 Dq2 DPq ANN; unfold rsize in *; lia)
           end.
           hide CDNE. hide ADNE. hide DNEW.
           chunk_facts RT AF GP cmapd 24.
           lazymatch goal with |- cps _ (ASTA RT ?S _ _) _ =>
             assert (FRSn : rt_frames RT S = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity) end.
           fframe_chunk RT AF fr 1%nat 128 cmapd 24.
           refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. park_disj.
           (* [comment removed for export] *)
           clear_acc.
           walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16); (pixd + 48, pixd + 56)] [0x8faf4].
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac|
                         split; [intros zz Hzz; right; right; left; exists pixd, 64; split; [solve [in_live_tac]| lia]| exact I]]]]).
    lazymatch goal with MUx : munch _ ?mm _ |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; destruct Hx as [_ Hx2]; cbn [outside] in Hx2;
                                         unfold shad, SHB in *; repeat split; try exact I; first [tauto | lia | Z.div_mod_to_equations; lia]) end.
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *.
           walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16); (pixd + 48, pixd + 56)] [0x8fb20].
           clear_acc.
           cwalk [0x8fb24].
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac|
                         split; [intros zz Hzz; right; right; left; exists pixd, 64; split; [solve [in_live_tac]| lia]| exact I]]]]).
    lazymatch goal with MUx : munch _ ?mm _ |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; destruct Hx as [_ Hx2]; cbn [outside] in Hx2;
                                         unfold shad, SHB in *; repeat split; try exact I; first [tauto | lia | Z.div_mod_to_equations; lia]) end.
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *.
           walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16); (pixd + 48, pixd + 56)] [0x8fb28].
           lstep. shbr8z.
           cwalk [0x91944; 0x8d86c; 0x8fcbc].
           (* [comment removed for export] *)
           split_at FRM 5%nat FRt. split_at FRt 1%nat FRtail. split_last_CB FRt [24; 4; 12]%nat.
           split_at FRt 1%nat FRv2. split_at FRv2 1%nat FRv2r.
           destruct (cb4_c4 _ _ _ FRv2) as (v2 & VC2). clear FRv2.
           pose proof FSH as T1; split_at T1 8%nat SHV2; split_at SHV2 1%nat T3; clear T1 T3.
      at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac|
                           split; [intros zz Hzz; right; right; left; exists pixd, 64; split; [solve [in_live_tac]| lia]| exact I]]]])
                    ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; destruct Hx as [_ Hx2]; cbn [outside] in Hx2;
                                    unfold shad, SHB in *; repeat split; try exact I; first [tauto | lia | Z.div_mod_to_equations; lia]).
           eapply cps_seq.
           { eapply VLD with (lo := lo) (cmap := cmapd) (pix := 0) (pv := fr + 64) (cv := cvn) (v := mkPixv 0 0 0 0 0 0 0 0 0 0 0) (x := v2); rt_side idtac.
             all: lazymatch goal with
                  | |- cmap_obj _ _ _ _ =>
                      unfold cmap_obj, cmap_cells, chunk;
                      split; [eexists; exact CMCn|]; split; [split; [solve [in_live_tac]| split; [assumption| split; [assumption| lia]]]|];
                      split; [split; [solve [in_live_tac]| split; [assumption| split; [assumption| assumption]]]|]; split; [exact CMOKn| unfold hid in NEQAn; exact NEQAn]
                  | |- _ \/ _ => left; reflexivity
                  | |- optrF _ _ _ _ _ =>
                      unfold optrF, own_frame; unfold parked in *; split;
                      [ exists fr, 1%nat; change (fs_size 1) with 128;
                        split; [solve [frames_in_tac]|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
                        split; [lia|]; split; [ul|];
                        lazymatch type of SHV2 with rw_cells _ _ ?A _ => replace (shad (fr + 64)) with A by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia) end;
                        destruct SHV2 as [[_ B] _]; exact B
                      | split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|]; split; [lia| right; ul] ]
                  | |- rw_cells _ _ _ [C4 _] => exact VC2
                  | |- lenv _ _ _ _ _ _ => lenv_tac
                  | |- lres _ _ _ _ _ => lres_tac
                  | |- ?g => idtac "LEFTOVER:" g
                  end. }
           after_call RT AF.
           fold_ag ltac:(fun Hx => pose proof (NFA _ Hx) as [N1 _]; destruct Hx as [Hx1 _];
                         first [ split; [apply (aclient_mono _ _ usp _ _ _ _ Hx1); [solve [live_add_tac]| solve [frames_sub_tac]| lia]
                                        | cbn [outside]; split; [lia| exact I]]
                               | apply (aclient_mono _ _ usp _ _ _ _ Hx1); [solve [live_add_tac]| solve [frames_sub_tac]| lia] ]).
           refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. park_disj.
           lazymatch goal with H : rw_cells asegs _ (fr + 64) [C4 _] |- _ => rename H into VC3 end.
           walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16); (pixd + 48, pixd + 56)] [0x8d86c; 0x8fcbc].
           clear SHV2. try clear SHV.
           if_cases HV2; clear HV2.
           ++ (* [comment removed for export] *)
              cwalk [0x8fcbc].
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac|
                         split; [intros zz Hzz; right; right; left; exists pixd, 64; split; [solve [in_live_tac]| lia]| exact I]]]]).
    lazymatch goal with MUx : munch _ ?mm _ |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; destruct Hx as [_ Hx2]; cbn [outside] in Hx2;
                                         unfold shad, SHB in *; repeat split; try exact I; first [tauto | lia | Z.div_mod_to_equations; lia]) end.
    to_entry.
              eapply EPI with (cmapd := cmapd) (cv' := cvn); try eassumption.
              all: lazymatch goal with
                   | |- wr_at asegs _ _ 120 => eassumption
                   | |- wr_at asegs _ _ 16 => exact (proj2 FSH)
                   | |- rw_cells asegs _ _ (pix_cells _) => unfold pix_cells, pixv_cmap; cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data]; exact PXDC
                   | |- _ <= _ => repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end; lia
                   | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
                   | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
                   | |- forall e, In e _ -> In e _ => solve [live_add_tac]
                   | |- _ \/ _ =>
                       right; unfold hid in CNZ, CDNE, ADNE, DNEW, PCNZ, NEQAn; destruct DNEW as [DN1 DN2];
                       split; [exact CNZ|]; split;
                       [ unfold cmap_obj, cmap_cells, chunk;
                         split; [eexists; exact CMCn|]; split; [split; [solve [in_live_tac]| split; [assumption| split; [assumption| lia]]]|];
                         split; [split; [solve [in_live_tac]| split; [assumption| split; [assumption| assumption]]]|]; split; [exact CMOKn| exact NEQAn] |];
                       split; [exact CDNE|]; split; [exact ADNE|]; split; [exact DN1|]; split; [exact DN2|]; split; [exact PCNZ|];
                       split; [exact EQD|]; split; [exact EQNA|]; split; [exact EQN|];
                       repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity
                   | |- ?g => idtac "LEFTOVER:" g
                   end.
           ++ (* [comment removed for export] *)
              cwalk [0x8d86c; 0x8fcbc].
      at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac|
                           split; [intros zz Hzz; right; right; left; exists pixd, 64; split; [solve [in_live_tac]| lia]| exact I]]]])
                    ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; destruct Hx as [_ Hx2]; cbn [outside] in Hx2;
                                    unfold shad, SHB in *; repeat split; try exact I; first [tauto | lia | Z.div_mod_to_equations; lia]).
        eapply cps_seq.
        { eapply RE with (lo := lo); rt_side idtac.
          all: lazymatch goal with
               | |- exists l, In _ LEPT_LITS => rewrite ?unsigned_lit by lia; lit_in
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- (_ < _)%nat => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; cbn [length]; unfold FRAMES_MAX in *; lia
               | |- _ <= rt_credit _ _ => repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end; lia
               | |- ?g => idtac "LEFTOVER:" g
               end. }
        after_call RT AF.
        fold_ag ltac:(fun Hx => destruct Hx as [Hx1 _]; apply (aclient_mono _ _ usp _ _ _ _ Hx1); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| lia]).
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. park_disj.
        walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16); (pixd + 48, pixd + 56)] [0x8fcbc].
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac|
                         split; [intros zz Hzz; right; right; left; exists pixd, 64; split; [solve [in_live_tac]| lia]| exact I]]]]).
    lazymatch goal with MUx : munch _ ?mm _ |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; destruct Hx as [_ Hx2]; cbn [outside] in Hx2;
                                         unfold shad, SHB in *; repeat split; try exact I; first [tauto | lia | Z.div_mod_to_equations; lia]) end.
    to_entry.
              eapply EPI with (cmapd := cmapd) (cv' := cvn); try eassumption.
              all: lazymatch goal with
                   | |- wr_at asegs _ _ 120 => eassumption
                   | |- wr_at asegs _ _ 16 => exact (proj2 FSH)
                   | |- rw_cells asegs _ _ (pix_cells _) => unfold pix_cells, pixv_cmap; cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data]; exact PXDC
                   | |- _ <= _ => repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end; lia
                   | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
                   | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
                   | |- forall e, In e _ -> In e _ => solve [live_add_tac]
                   | |- _ \/ _ =>
                       right; unfold hid in CNZ, CDNE, ADNE, DNEW, PCNZ, NEQAn; destruct DNEW as [DN1 DN2];
                       split; [exact CNZ|]; split;
                       [ unfold cmap_obj, cmap_cells, chunk;
                         split; [eexists; exact CMCn|]; split; [split; [solve [in_live_tac]| split; [assumption| split; [assumption| lia]]]|];
                         split; [split; [solve [in_live_tac]| split; [assumption| split; [assumption| assumption]]]|]; split; [exact CMOKn| exact NEQAn] |];
                       split; [exact CDNE|]; split; [exact ADNE|]; split; [exact DN1|]; split; [exact DN2|]; split; [exact PCNZ|];
                       split; [exact EQD|]; split; [exact EQNA|]; split; [exact EQN|];
                       repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity
                   | |- ?g => idtac "LEFTOVER:" g
                   end.
Qed.
End CC.
