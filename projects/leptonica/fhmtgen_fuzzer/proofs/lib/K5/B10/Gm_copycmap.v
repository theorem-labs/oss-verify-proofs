(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import ImageA.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import Layout.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_lits Lept_env LeptC_kit Lept_chain Lept_leaf Lept_objkit Lept_fuzzkit Lept_deserkit D_iface D_defs Gm_iface Gm_kit Gm_leaf LeptB_guard LeptB_guard2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac lia ::= first [ zify_prune; first [ zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker | Zify.zify; xlia zchecker ] | Zify.zify; xlia zchecker ].   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition CCM_AFTER_POISON : Z := 0x93584.
Definition CCM_EPI : Z := 0x9382c.
Definition CCM_FLAG_LOAD : Z := 0x93888.
Definition CCM_FLAG_DONE : Z := 0x93890.

(* [comment removed for export] *)
Ltac ccm_resync RT AF GP AGF PFS NFA :=
  cps_stop;
  art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]);
  lazymatch goal with MUx : munch _ ?mm _ |- _ =>
    agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                       repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end;
  refresh RT AF; lib_refresh RT GP; unfold shad, SHB in *; park_disj.

Section CCM.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis IVN : pixcmapIsValid_null_cps RT.
Hypothesis CMC : pixcmapCopy_cps RT.

Theorem pixCopyColormap_ok : pixCopyColormap_cps RT.
Proof using AF RC GP IVN CMC.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    pixd pixs vd vs cvd cvs ras FDO MST -> -> -> POD POS NEQ DEQ CM0 UCX ENV RES.
  unfold lpost, lenv, lres, keeps, keepsL in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct RES as (FRB & LVB & CRB & LVP). unfold uctx in UCX.
  pose proof POD as (PXD & (PDIN & PD0 & PD16 & _) & HOKD & _ & _).
  pose proof POS as (PXS & (PSIN & PS0 & PS16 & _) & HOKS & _ & PSCM).
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  pose proof (bv_unsigned_in_range 64 ra) as RRA. pose proof (bv_unsigned_in_range 64 s0) as RS0.
  unfold bv_modulus in RRA, RS0. change (2 ^ Z.of_N 64) with (2^64) in RRA, RS0.
  unfold entry_st, e_pixCopyColormap, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold LSTK, STDERR_STACK in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  pose proof ST as (STa & STb & _).
  lib_refresh RT GP.
  pose proof IVN as IV. unfold pixcmapIsValid_null_cps in IV. pose proof CMC as CC. unfold pixcmapCopy_cps in CC.
  set (PF := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a /\ outside [(pixd + 48, pixd + 56)] a).
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a [Ha _]. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]. }
  pose proof (live_apart RT AF Σ m pixd 64 pixs 64 ART0 PDIN PSIN NEQ) as DPS.
  chunk_facts RT AF GP pixd 64. chunk_facts RT AF GP pixs 64.
  unfold pix_cells in PXD, PXS. rewrite CM0 in PXD.
  assert (DBND : 1 <= p_d vs <= 32) by (destruct HOKS as (HD1 & _); cbn [In] in HD1; lia).
  hide POD. hide POS. hide PSCM.
  assert (AL : usp mod 32 = 0 \/ usp mod 32 = 16) by (Z.div_mod_to_equations; lia).
  destruct AL as [AL|AL].
  - (* [comment removed for export] *)

    park_disj. carve_frame 96%nat ST.
    clear_acc.
    Time walk_to AF MST [(usp - 96, usp)] [e_stack_malloc 1%nat].
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
    eapply cps_seq.
    { pose proof (gp_stack_malloc_1 RT GP) as SM1; unfold stack_malloc_contract' in SM1; eapply SM1 with (lo := lo); rt_side idtac. }
    after_call RT AF.
    fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]).
    fframe_open RT AF PF (rt_live RT Σ) usp 1%nat 128 ltac:(fun Ha => exact (proj1 Ha)).
    pose proof (proj2 FRM) as WRF0. cbn [cells_size csize Nat.add] in WRF0. change (Z.of_nat 120) with 120 in WRF0. hide WRF0.
    fframe_chunk RT AF fr 1%nat 128 pixd 64.
    fframe_chunk RT AF fr 1%nat 128 pixs 64.
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
    Time walk_to AF MST [(usp - 96, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x93584].
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
    lazymatch goal with MUx : munch _ ?mm _ |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                         repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. park_disj.
    (* [comment removed for export] *)
    lazymatch goal with FRx : rw_cells asegs _ (usp + -96) ?cs |- _ =>
      assert (EPI : forall (S : rts RT) (mE : mem) (cmapd : Z) (cvn : cmapv)
                (r1 r5 r6 r7 r9 r10 r11 r12 r13 r14 r15 r16 r17 r19 r20 r21 r24 r25 r28 r29 r30 r31 : word) F' fc',
          ART RT S mE -> mem_inv asegs mE -> stk asegs mE lo (usp + -96) -> rw_cells asegs mE (usp + -96) cs ->
          wr_at asegs mE fr 120 -> wr_at asegs mE (fr / 8 + 2147450880) 16 ->
          LIBH mE -> io_ssp mE -> agree_on PF m mE -> wmono asegs m mE ->
          rw_cells asegs mE pixd (pix_cells (mkPixv (p_w vd) (p_h vd) (p_d vd) (p_spp vd) (p_wpl vd) (p_xres vd) (p_yres vd) (p_inf vd) (p_spec vd) cmapd (p_data vd))) ->
          In (pixd, 64) (rt_live RT S) ->
          (cmapd = 0 \/ (cmap_obj (rt_live RT S) mE cmapd cvn /\ c_depth cvn = c_depth cvs)) ->
          (p_cmap vs = 0 -> cmapd = 0) -> (p_cmap vs <> 0 -> cmapd <> 0) ->
          rt_live RT S = (if cmapd =? 0 then rt_live RT Σ else (c_arr cvn, 4 * c_nalloc cvn) :: (cmapd, 24) :: rt_live RT Σ) ->
          rt_frames RT S = (fr, 1%nat) :: rt_frames RT Σ -> rt_sp0 RT S = rt_sp0 RT Σ -> rt_credit RT Σ - 4 <= rt_credit RT S ->
          cps asegs (ASTA RT S PMc (eq (entry_st r1 (Z_to_bv 64 (usp + -96)) gp (Z_to_bv 64 TP_A) r5 r6 r7 (Z_to_bv 64 usp) r9
                                          r10 r11 r12 r13 r14 r15 r16 r17 (Z_to_bv 64 fr) r19 r20 r21 (Z_to_bv 64 (fr / 8 + 2147450880))
                                          (Z_to_bv 64 fr) r24 r25 s10 s11 r28 r29 r30 r31 F' fc' 0x9382c mE))) QF) end.
    { intros S mE cmapd cvn r1 r5 r6 r7 r9 r10 r11 r12 r13 r14 r15 r16 r17 r19 r20 r21 r24 r25 r28 r29 r30 r31 F' fc'
        ARTE MIE STE FRE WFE WSE LHE SSPE AGE WME PXE PINE HCM HC0 HC1 ELV EFR ESP0 ECR.
      clear AGF. rename AGE into AGF.
      pose proof PXE as PXEk. hide PXEk.
      repeat match goal with H : rw_cells asegs _ _ _ |- _ => lazymatch H with FRE => fail | _ => clear H end end.
      unfold hid in PXEk. rename PXEk into PXE.
      repeat match goal with H : ro_cells asegs _ _ _ |- _ => clear H end.
      repeat match goal with H : ART RT _ _ |- _ => lazymatch H with ARTE => fail | _ => clear H end end.
      repeat match goal with H : LIBH _ |- _ => lazymatch H with LHE => fail | _ => clear H end end.
      repeat match goal with H : io_ssp _ |- _ => lazymatch H with SSPE => fail | _ => clear H end end.
      repeat match goal with H : stk asegs _ _ _ |- _ => lazymatch H with STE => fail | _ => clear H end end.
      repeat match goal with H : mem_inv asegs _ |- _ => lazymatch H with MIE => fail | _ => clear H end end.
      repeat match goal with H : wmono asegs _ _ |- _ => lazymatch H with WME => fail | _ => clear H end end.
      repeat match goal with H : munch _ _ _ |- _ => clear H end.
      repeat match goal with H : rt_frames RT _ = _ |- _ => lazymatch H with EFR => fail | _ => clear H end end.
      repeat match goal with H : rt_live RT _ = _ |- _ => lazymatch H with ELV => fail | _ => clear H end end.
      repeat match goal with H : rt_sp0 RT _ = _ |- _ => lazymatch H with ESP0 => fail | _ => clear H end end.
      repeat match goal with H : rt_credit RT _ = _ |- _ => clear H end.
      clear_acc.
      assert (LSUB : forall e, In e (rt_live RT Σ) -> In e (rt_live RT S))
        by (intros e He; rewrite ELV; destruct (cmapd =? 0); [exact He| right; right; exact He]).
      hide ELV. pose proof PXE as PXEh. hide PXEh. clear PXE.
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
        cbn [outside].
        repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]. }
      unfold entry_st.
      Time walk_to AF MST [(usp - 96, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x93888].
      lazymatch goal with MUx : munch _ mE ?mc |- _ =>
        assert (KEEP1 : keeps_live (rt_live RT S) mE mc)
          by (let bb := fresh "bb" in let kk := fresh "kk" in let Hb := fresh "Hb" in let a := fresh "a" in let Ha := fresh "Ha" in
              intros bb kk Hb a Ha; apply MUx; exact (LOUT bb kk Hb _ Ha)) end.
      Time frame_release_k RT AF GP MST Σ fr 1%nat 128 PF AGF PFS usp lo 0x93890
        ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
        ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                          repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia])
        ltac:(fun Hx => exact (proj1 Hx))
        ltac:(fun fl FLN => idtac).
      Time walk_to AF MST [(usp - 96, usp)] (@nil Z).
      cps_stop.
      art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I]).
      lazymatch goal with MUx : munch _ ?mm ?mc |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
        assert (KEEP3 : keeps_live (rt_live RT S) mm mc)
          by (let bb := fresh "bb" in let kk := fresh "kk" in let Hb := fresh "Hb" in let a := fresh "a" in let Ha := fresh "Ha" in
              intros bb kk Hb a Ha; apply MUx; cbn [outside]; split; [exact (proj1 (LOUT bb kk Hb _ Ha))| exact I]);
        agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]) end.
      lazymatch goal with K3 : keeps_live _ _ ?mc |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
        assert (KEEPF : keeps_live (rt_live RT S) mE mc)
          by (eapply keeps_live_trans; [exact KEEP1|]; eapply keeps_live_trans; [exact KEEPR| exact K3]) end.
      apply cps_finish. intros c Hc. subst QF. cbv beta.
      lazymatch type of Hc with ASTA RT ?S' _ _ _ => exists S' end. eexists. exists cmapd, cvn.
      split.
      { eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-. eexists.
        split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
        split; [split; [split; [assumption| split; [assumption| split; [| assumption]]]| split; assumption]|].
        { repeat match goal with H : wmono asegs _ _ |- _ => revert H end. clear. intros. eauto using wmono_trans. }
        split; [intros a Ha Ho; exact (AGF a (conj Ha Ho))|].
        split; [apply (keeps_live_cells (rt_live RT S) mE _ pixd 64 pixd _ KEEPF PINE); [lia| unfold pix_cells; cbn [cells_size csize Nat.add]; lia| unfold hid in PXEh; exact PXEh]|].
        destruct HCM as [HZ|(HO & HDP)]; [left; exact HZ| right]. split; [| exact HDP].
        rewrite LV2. exact (cmap_obj_keep _ mE _ cmapd cvn KEEPF HO). }
      unfold hid in ELV. rewrite LV2, FRS2, SP2, CR2.
      split; [exact HC0|]. split; [exact HC1|]. split; [exact ELV|]. split; [reflexivity|]. split; [exact ESP0| lia]. }
    unfold hid in PSCM. rewrite <- DEQ in PXS.
    destruct PSCM as [CMS0|(CMSO & NS1 & NS2 & NS3 & NS4)].
    + (* [comment removed for export] *)
      rewrite CMS0 in PXS.
      (* [comment removed for export] *)
      Time walk_to AF MST [(usp - 96, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x935d8].
      ccm_resync RT AF GP AGF PFS NFA.
      Time walk_to AF MST [(usp - 96, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x99d38; 0x93618].
      cwalk [0x99d38; 0x93618].
      ccm_resync RT AF GP AGF PFS NFA.
      Time walk_to AF MST [(usp - 96, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x99d38; 0x995fc; 0x99320; 0x912bc; 0x9382c].
      cwalk [0x99d38; 0x995fc; 0x99320; 0x912bc; 0x9382c].
      cps_stop.
      art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
      lazymatch goal with MUx : munch _ ?mm _ |- _ =>
        agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                           repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
      to_entry.
      eapply EPI with (cmapd := 0) (cvn := mkCmapv 0 0 0 0); try eassumption.
      all: lazymatch goal with
           | |- wr_at asegs _ _ 120 => first [exact (proj2 FRM) | eassumption]
           | |- wr_at asegs _ _ 16 => exact (proj2 FSH)
           | |- rw_cells asegs _ _ (pix_cells _) => unfold pix_cells; cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data]; exact PXD
           | |- In _ _ => solve [in_live_tac]
           | |- _ \/ _ => left; reflexivity
           | |- _ = 0 -> _ => intros _; reflexivity
           | |- _ <> 0 -> _ => intros NZ; exfalso; exact (NZ CMS0)
           | |- _ <= _ => repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end; lia
           | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
           | |- rt_live _ _ = _ => change (0 =? 0) with true; cbv iota; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity
           | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
           | |- ?g => idtac "LEFT:" g
           end.
    + (* [comment removed for export] *)
      set (cms := p_cmap vs) in *.
      pose proof CMSO as (_ & (INCS & CMS0 & _) & _).
      assert (CMSNZ : cms <> 0) by lia.
      destruct (UCX CMSNZ) as (UCH & TRM). clear UCX.
      pose proof (live_apart2 RT AF Σ m cms 24 pixd 64 ART0 INCS PDIN ltac:(intros E; inversion E)) as DCP.
      assert (CMSPF : forall a, cms <= a < cms + 24 -> PF a).
      { intros a Ha. split; [right; right; left; exists cms, 24; split; [exact INCS| exact Ha]| cbn [outside]; split; [lia| exact I]]. }
      hide CMSO. hide CMSPF.
      chunk_facts RT AF GP cms 24.
      Time walk_to AF MST [(usp - 96, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x935d8].
      ccm_resync RT AF GP AGF PFS NFA.
      Time walk_to AF MST [(usp - 96, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x99d38; 0x93618].
      cwalk [0x99d38; 0x93618].
      ccm_resync RT AF GP AGF PFS NFA.
      Time walk_to AF MST [(usp - 96, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x99d38; 0x995fc; 0x99320; 0x912bc; 0x9382c].
      cwalk [0x99d38; 0x995fc; 0x99320; 0x912bc; 0x9382c].
      (* [comment removed for export] *)
      split_last_CB FRM [24%nat; 4%nat; 4%nat]. split_at FRM 6%nat FRV. split_at FRV 1%nat FRT.
      destruct (cb4_c4' _ _ _ FRV) as (xv & PVC). clear FRV.
      pose proof FSH as SHV. split_at SHV 14%nat SHV2. split_at SHV2 1%nat SHV3. clear SHV SHV3.
      at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                    ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                          repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
      unfold hid in CMSO, CMSPF.
      lazymatch type of AGF with agree_on _ _ ?mc =>
        assert (CMSO1 : cmap_obj (rt_live RT Σ) mc cms cvs) by (exact (cmap_obj_agree (rt_live RT Σ) PF m mc cms cvs CMSO AGF CMSPF)) end.
      hide CMSO. hide CMSPF.
      eapply cps_seq.
      { eapply IV with (lo := lo) (cmap := cms) (pv := fr + 112) (cv := cvs) (x := xv); rt_side idtac.
        all: lazymatch goal with
             | |- cmap_obj _ _ _ _ => repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact CMSO1
             | |- optrV _ _ _ _ _ =>
                 left; unfold optrF, parked in *; split;
                 [ exists fr, 1%nat; rewrite FRS; change (fs_size 1) with 128;
                   split; [left; reflexivity|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
                   split; [lia|]; split; [lia|];
                   replace (shad (fr + 112)) with (fr / 8 + 2147450894) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
                   destruct SHV2 as [[_ B] _]; exact B
                 | unfold SEGTOP_A; repeat split; first [lia | clear - FR64; Z.div_mod_to_equations; lia] ]
             | |- lenv _ _ _ _ _ _ => lenv_tac
             | |- lres _ _ _ _ _ => lres_tac
             | |- ?g => idtac "LEFT:" g
             end. }
      clear SHV2 CMSO1.
      after_call RT AF.
      fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]|
                                      cbn [outside]; destruct (NFA _ Hx) as [N1 N2]; split; [lia| exact I]]).
      refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
      Time walk_to AF MST [(usp - 96, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x99d38; 0x995fc; 0x99320; 0x912bc; 0x9382c].
      cwalk [0x99d38; 0x995fc; 0x99320; 0x912bc; 0x9382c].
      (* [comment removed for export] *)
      pose proof FR as FRrec. split_at FRrec 10%nat FRrec2. split_at FRrec2 2%nat FRrest. clear FRrec FRrest.
      at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                    ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                          repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
      unfold hid in CMSO, CMSPF.
      lazymatch type of AGF with agree_on _ _ ?mc =>
        assert (CMSO1 : cmap_obj (rt_live RT Σ) mc cms cvs) by (exact (cmap_obj_agree (rt_live RT Σ) PF m mc cms cvs CMSO AGF CMSPF)) end.
      hide CMSO. hide CMSPF.
      assert (RALO : 4096 <= bv_unsigned ra).
      { pose proof traces_ra_lo' as TLO. rewrite Forall_forall in TLO. specialize (TLO _ TRM).
        apply Forall_inv_tail in TLO. apply Forall_inv in TLO. exact TLO. }
      eapply cps_seq.
      { eapply CC with (lo := lo) (cmaps := cms) (cvs := cvs) (ra1 := bv_unsigned ra) (ras := ras); rt_side idtac.
        all: lazymatch goal with
             | |- cmap_obj _ _ _ _ => repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact CMSO1
             | |- uctx _ _ _ _ =>
                 unfold uctx; rewrite ?unsigned_lit by ul;
                 apply (chain_ok_push _ (usp + -96) usp (bv_unsigned ra) (bv_unsigned s0) ras);
                   [ lia | clear - SPA; Z.div_mod_to_equations; lia | ul | lia | lia
                   | rewrite !Z_to_bv_bv_unsigned; exact FRrec2 | ];
                 apply (chain_ok_keep ras m _ usp (bv_unsigned s0) UCH);
                 eapply agree_sub; [exact AGF|]; intros zx Hzx; split; [left; exact Hzx| cbn [outside]; unfold parked in *; split; [lia| exact I]]
             | |- In _ CLIENT_TRACES => exact TRM
             | |- lenv _ _ _ _ _ _ => lenv_tac
             | |- lres _ _ _ _ _ => lres_tac
             | |- ?g => idtac "LEFT:" g
             end. }
      clear CMSO1 FRrec2.
      after_call RT AF.
      fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]| exact I]).
      lazymatch goal with H : cmap_obj _ _ ?p ?cv |- _ => rename H into CMDO; set (cmapd := p) in *; set (cvn := cv) in * end.
      lazymatch goal with H : rt_live RT _ = (c_arr cvn, _) :: _ |- _ => rename H into LVN end.
      lazymatch goal with H : c_depth cvn = _ |- _ => rename H into CDEQ end.
      pose proof CMDO as ((padd & CMDC) & (INCD & CD0 & CD16 & _) & (INAD & AD0 & AD16 & ADN) & CMOKD & NEQD).
      set (ard := c_arr cvn) in *. set (nad := 4 * c_nalloc cvn) in *.
      (* [comment removed for export] *)
      lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ =>
        assert (SUBC : forall e, In e (rt_live RT Σ) -> In e (rt_live RT S) /\ fst e <> cmapd)
          by (intros e He; split; [rewrite LVN; right; right; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact He|];
              apply (fresh_chunk_ne RT AF S mm [(ard, nad)] cmapd 24 _ e A LVN);
              [ cbn [app]; right; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact He | lia | destruct e as [eq ek]; exact (LVP eq ek He) ]);
        assert (SUBA : forall e, In e (rt_live RT Σ) -> In e (rt_live RT S) /\ fst e <> ard)
          by (intros e He; split; [rewrite LVN; right; right; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact He|];
              apply (fresh_chunk_ne RT AF S mm [] ard nad _ e A LVN);
              [ cbn [app]; right; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact He | lia | destruct e as [eq ek]; exact (LVP eq ek He) ]);
        assert (NCMD : forall a, PF a -> a < cmapd \/ cmapd + 24 <= a)
          by (intros a Ha; apply (inner_chunk_apart RT AF S mm cmapd 24 (rt_live RT Σ) (rt_frames RT Σ) usp a A INCD SUBC);
              [ solve [frames_sub_tac] | repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul | exact (proj1 Ha) ]);
        assert (NARD : forall a, PF a -> a < ard \/ ard + nad <= a)
          by (intros a Ha; apply (inner_chunk_apart RT AF S mm ard nad (rt_live RT Σ) (rt_frames RT Σ) usp a A INAD SUBA);
              [ solve [frames_sub_tac] | repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul | exact (proj1 Ha) ]);
        pose proof (live_apart2 RT AF S mm cmapd 24 pixd 64 A INCD ltac:(solve [in_live_tac]) ltac:(intros E; inversion E)) as DCD end.
      chunk_facts RT AF GP cmapd 24.
      lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ =>
        assert (FRSn : rt_frames RT S = (fr, 1%nat) :: rt_frames RT Σ)
          by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity) end.
      fframe_chunk RT AF fr 1%nat 128 cmapd 24.
      unfold cmap_cells in CMDC.
      hide CMDO. hide SUBC. hide SUBA.
      refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
      Time walk_to AF MST [(usp - 96, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x99d38; 0x995fc; 0x99320; 0x912bc; 0x9382c; 0x93664].
      ccm_resync RT AF GP AGF PFS NFA.
      Time walk_to AF MST [(usp - 96, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x99d38; 0x93694].
      cwalk [0x99d38; 0x93694].
      ccm_resync RT AF GP AGF PFS NFA.
      Time walk_to AF MST [(usp - 96, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x93698].
      lstep.
      shbr0_keep.
      ccm_resync RT AF GP AGF PFS NFA.
      Time walk_to AF MST [(usp - 96, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16); (pixd + 48, pixd + 56)] [0x99d38; 0x995fc; 0x99320; 0x912bc; 0x9382c].
      (* [comment removed for export] *)
      split_at FRM 6%nat FRM2. split_last_CB FRM [24%nat; 4%nat; 12%nat]. split_at FRM 6%nat FRW. split_at FRW 1%nat FRW2.
      destruct (cb4_c4' _ _ _ FRW) as (xw & PWC). clear FRW.
      pose proof FSH as SHW. split_at SHW 8%nat SHW2. split_at SHW2 1%nat SHW3. clear SHW SHW3.
      at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac|
                            split; [intros zz Hzz; right; right; left; exists pixd, 64; split; [solve [in_live_tac]| lia]| exact I]]]])
                    ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; destruct Hx as [_ HxO];
                          cbn [outside] in HxO; unfold shad, SHB in *; repeat split; try exact I; first [lia | tauto | Z.div_mod_to_equations; lia]).
      lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ =>
        assert (CMDO2 : cmap_obj (rt_live RT S) mm cmapd cvn)
          by (split; [exists padd; unfold cmap_cells; exact CMDC|];
              split; [split; [exact INCD| split; [exact CD0| split; [exact CD16| lia]]]|];
              split; [split; [exact INAD| split; [exact AD0| split; [exact AD16| exact ADN]]]|];
              split; [exact CMOKD| exact NEQD]) end.
      eapply cps_seq.
      { eapply IV with (lo := lo) (cmap := cmapd) (pv := fr + 64) (cv := cvn) (x := xw); rt_side idtac.
        all: lazymatch goal with
             | |- cmap_obj _ _ _ _ => exact CMDO2
             | |- optrV _ _ _ _ _ =>
                 left; unfold optrF, parked in *; split;
                 [ exists fr, 1%nat; rewrite FRSn; change (fs_size 1) with 128;
                   split; [left; reflexivity|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
                   split; [lia|]; split; [lia|];
                   replace (shad (fr + 64)) with (fr / 8 + 2147450888) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
                   destruct SHW2 as [[_ B] _]; exact B
                 | unfold SEGTOP_A; repeat split; first [lia | clear - FR64; Z.div_mod_to_equations; lia] ]
             | |- lenv _ _ _ _ _ _ => lenv_tac
             | |- lres _ _ _ _ _ => lres_tac
             | |- ?g => idtac "LEFT:" g
             end. }
      clear SHW2 CMDO2.
      after_call RT AF.
      fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [solve [live_add_tac]| solve [frames_sub_tac]| lia]|
                                      cbn [outside]; destruct (NFA _ Hx) as [N1 N2]; split; [lia| exact I]]).
      refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
      Time walk_to AF MST [(usp - 96, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x99d38; 0x995fc; 0x99320; 0x912bc; 0x9382c].
      cwalk [0x99d38; 0x995fc; 0x99320; 0x912bc; 0x9382c].
      cps_stop.
      art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
      lazymatch goal with MUx : munch _ ?mm _ |- _ =>
        agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                           repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
      lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ =>
        assert (CMDO3 : cmap_obj (rt_live RT S) mm cmapd cvn)
          by (split; [exists padd; unfold cmap_cells; exact CMDC|];
              split; [split; [solve [in_live_tac]| split; [exact CD0| split; [exact CD16| lia]]]|];
              split; [split; [solve [in_live_tac]| split; [exact AD0| split; [exact AD16| exact ADN]]]|];
              split; [exact CMOKD| exact NEQD]) end.
      to_entry.
      eapply EPI with (cmapd := cmapd) (cvn := cvn); try eassumption.
      all: lazymatch goal with
           | |- wr_at asegs ?mc _ 120 =>
               unfold hid in WRF0; lazymatch type of WRF0 with wr_at asegs ?m0 _ _ =>
                 lazymatch goal with WMx : wmono asegs m0 mc |- _ => exact (wr_at_transport asegs m0 mc _ _ WRF0 WMx) end end
           | |- wr_at asegs _ _ 16 => exact (proj2 FSH)
           | |- rw_cells asegs _ _ (pix_cells _) => unfold pix_cells; cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data]; exact PXD
           | |- In _ _ => solve [in_live_tac]
           | |- _ \/ _ => right; split; [exact CMDO3| exact CDEQ]
           | |- _ = 0 -> _ => intros Z0; exfalso; exact (CMSNZ Z0)
           | |- _ <> 0 -> _ => intros _; lia
           | |- _ <= _ => repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end; lia
           | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
           | |- rt_live _ _ = _ => replace (cmapd =? 0) with false by (symmetry; apply Z.eqb_neq; lia); repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity
           | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
           | |- ?g => idtac "LEFT:" g
           end.

  -

    park_disj. carve_frame 112%nat ST.
    clear_acc.
    Time walk_to AF MST [(usp - 112, usp)] [e_stack_malloc 1%nat].
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
    eapply cps_seq.
    { pose proof (gp_stack_malloc_1 RT GP) as SM1; unfold stack_malloc_contract' in SM1; eapply SM1 with (lo := lo); rt_side idtac. }
    after_call RT AF.
    fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]).
    fframe_open RT AF PF (rt_live RT Σ) usp 1%nat 128 ltac:(fun Ha => exact (proj1 Ha)).
    pose proof (proj2 FRM) as WRF0. cbn [cells_size csize Nat.add] in WRF0. change (Z.of_nat 120) with 120 in WRF0. hide WRF0.
    fframe_chunk RT AF fr 1%nat 128 pixd 64.
    fframe_chunk RT AF fr 1%nat 128 pixs 64.
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
    Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x93584].
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
    lazymatch goal with MUx : munch _ ?mm _ |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                         repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. park_disj.
    (* [comment removed for export] *)
    lazymatch goal with FRx : rw_cells asegs _ (usp + -112) ?cs |- _ =>
      assert (EPI : forall (S : rts RT) (mE : mem) (cmapd : Z) (cvn : cmapv)
                (r1 r5 r6 r7 r9 r10 r11 r12 r13 r14 r15 r16 r17 r19 r20 r21 r24 r25 r28 r29 r30 r31 : word) F' fc',
          ART RT S mE -> mem_inv asegs mE -> stk asegs mE lo (usp + -112) -> rw_cells asegs mE (usp + -112) cs ->
          wr_at asegs mE fr 120 -> wr_at asegs mE (fr / 8 + 2147450880) 16 ->
          LIBH mE -> io_ssp mE -> agree_on PF m mE -> wmono asegs m mE ->
          rw_cells asegs mE pixd (pix_cells (mkPixv (p_w vd) (p_h vd) (p_d vd) (p_spp vd) (p_wpl vd) (p_xres vd) (p_yres vd) (p_inf vd) (p_spec vd) cmapd (p_data vd))) ->
          In (pixd, 64) (rt_live RT S) ->
          (cmapd = 0 \/ (cmap_obj (rt_live RT S) mE cmapd cvn /\ c_depth cvn = c_depth cvs)) ->
          (p_cmap vs = 0 -> cmapd = 0) -> (p_cmap vs <> 0 -> cmapd <> 0) ->
          rt_live RT S = (if cmapd =? 0 then rt_live RT Σ else (c_arr cvn, 4 * c_nalloc cvn) :: (cmapd, 24) :: rt_live RT Σ) ->
          rt_frames RT S = (fr, 1%nat) :: rt_frames RT Σ -> rt_sp0 RT S = rt_sp0 RT Σ -> rt_credit RT Σ - 4 <= rt_credit RT S ->
          cps asegs (ASTA RT S PMc (eq (entry_st r1 (Z_to_bv 64 (usp + -112)) gp (Z_to_bv 64 TP_A) r5 r6 r7 (Z_to_bv 64 usp) r9
                                          r10 r11 r12 r13 r14 r15 r16 r17 (Z_to_bv 64 fr) r19 r20 r21 (Z_to_bv 64 (fr / 8 + 2147450880))
                                          (Z_to_bv 64 fr) r24 r25 s10 s11 r28 r29 r30 r31 F' fc' 0x9382c mE))) QF) end.
    { intros S mE cmapd cvn r1 r5 r6 r7 r9 r10 r11 r12 r13 r14 r15 r16 r17 r19 r20 r21 r24 r25 r28 r29 r30 r31 F' fc'
        ARTE MIE STE FRE WFE WSE LHE SSPE AGE WME PXE PINE HCM HC0 HC1 ELV EFR ESP0 ECR.
      clear AGF. rename AGE into AGF.
      pose proof PXE as PXEk. hide PXEk.
      repeat match goal with H : rw_cells asegs _ _ _ |- _ => lazymatch H with FRE => fail | _ => clear H end end.
      unfold hid in PXEk. rename PXEk into PXE.
      repeat match goal with H : ro_cells asegs _ _ _ |- _ => clear H end.
      repeat match goal with H : ART RT _ _ |- _ => lazymatch H with ARTE => fail | _ => clear H end end.
      repeat match goal with H : LIBH _ |- _ => lazymatch H with LHE => fail | _ => clear H end end.
      repeat match goal with H : io_ssp _ |- _ => lazymatch H with SSPE => fail | _ => clear H end end.
      repeat match goal with H : stk asegs _ _ _ |- _ => lazymatch H with STE => fail | _ => clear H end end.
      repeat match goal with H : mem_inv asegs _ |- _ => lazymatch H with MIE => fail | _ => clear H end end.
      repeat match goal with H : wmono asegs _ _ |- _ => lazymatch H with WME => fail | _ => clear H end end.
      repeat match goal with H : munch _ _ _ |- _ => clear H end.
      repeat match goal with H : rt_frames RT _ = _ |- _ => lazymatch H with EFR => fail | _ => clear H end end.
      repeat match goal with H : rt_live RT _ = _ |- _ => lazymatch H with ELV => fail | _ => clear H end end.
      repeat match goal with H : rt_sp0 RT _ = _ |- _ => lazymatch H with ESP0 => fail | _ => clear H end end.
      repeat match goal with H : rt_credit RT _ = _ |- _ => clear H end.
      clear_acc.
      assert (LSUB : forall e, In e (rt_live RT Σ) -> In e (rt_live RT S))
        by (intros e He; rewrite ELV; destruct (cmapd =? 0); [exact He| right; right; exact He]).
      hide ELV. pose proof PXE as PXEh. hide PXEh. clear PXE.
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
        cbn [outside].
        repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]. }
      unfold entry_st.
      Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x93888].
      lazymatch goal with MUx : munch _ mE ?mc |- _ =>
        assert (KEEP1 : keeps_live (rt_live RT S) mE mc)
          by (let bb := fresh "bb" in let kk := fresh "kk" in let Hb := fresh "Hb" in let a := fresh "a" in let Ha := fresh "Ha" in
              intros bb kk Hb a Ha; apply MUx; exact (LOUT bb kk Hb _ Ha)) end.
      Time frame_release_k RT AF GP MST Σ fr 1%nat 128 PF AGF PFS usp lo 0x93890
        ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
        ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                          repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia])
        ltac:(fun Hx => exact (proj1 Hx))
        ltac:(fun fl FLN => idtac).
      Time walk_to AF MST [(usp - 112, usp)] (@nil Z).
      lazymatch goal with ST' : stk asegs _ lo (usp + -112), FR' : rw_cells asegs _ (usp + -112) _ |- _ => release_frame FR' ST' usp end.
      cps_stop.
      art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I]).
      lazymatch goal with MUx : munch _ ?mm ?mc |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
        assert (KEEP3 : keeps_live (rt_live RT S) mm mc)
          by (let bb := fresh "bb" in let kk := fresh "kk" in let Hb := fresh "Hb" in let a := fresh "a" in let Ha := fresh "Ha" in
              intros bb kk Hb a Ha; apply MUx; cbn [outside]; split; [exact (proj1 (LOUT bb kk Hb _ Ha))| exact I]);
        agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]) end.
      lazymatch goal with K3 : keeps_live _ _ ?mc |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
        assert (KEEPF : keeps_live (rt_live RT S) mE mc)
          by (eapply keeps_live_trans; [exact KEEP1|]; eapply keeps_live_trans; [exact KEEPR| exact K3]) end.
      apply cps_finish. intros c Hc. subst QF. cbv beta.
      lazymatch type of Hc with ASTA RT ?S' _ _ _ => exists S' end. eexists. exists cmapd, cvn.
      split.
      { eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-. eexists.
        split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
        split; [split; [split; [assumption| split; [assumption| split; [| assumption]]]| split; assumption]|].
        { repeat match goal with H : wmono asegs _ _ |- _ => revert H end. clear. intros. eauto using wmono_trans. }
        split; [intros a Ha Ho; exact (AGF a (conj Ha Ho))|].
        split; [apply (keeps_live_cells (rt_live RT S) mE _ pixd 64 pixd _ KEEPF PINE); [lia| unfold pix_cells; cbn [cells_size csize Nat.add]; lia| unfold hid in PXEh; exact PXEh]|].
        destruct HCM as [HZ|(HO & HDP)]; [left; exact HZ| right]. split; [| exact HDP].
        rewrite LV2. exact (cmap_obj_keep _ mE _ cmapd cvn KEEPF HO). }
      unfold hid in ELV. rewrite LV2, FRS2, SP2, CR2.
      split; [exact HC0|]. split; [exact HC1|]. split; [exact ELV|]. split; [reflexivity|]. split; [exact ESP0| lia]. }
    unfold hid in PSCM. rewrite <- DEQ in PXS.
    destruct PSCM as [CMS0|(CMSO & NS1 & NS2 & NS3 & NS4)].
    + (* [comment removed for export] *)
      rewrite CMS0 in PXS.
      (* [comment removed for export] *)
      Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x935d8].
      ccm_resync RT AF GP AGF PFS NFA.
      Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x99d38; 0x93618].
      cwalk [0x99d38; 0x93618].
      ccm_resync RT AF GP AGF PFS NFA.
      Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x99d38; 0x995fc; 0x99320; 0x912bc; 0x9382c].
      cwalk [0x99d38; 0x995fc; 0x99320; 0x912bc; 0x9382c].
      cps_stop.
      art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
      lazymatch goal with MUx : munch _ ?mm _ |- _ =>
        agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                           repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
      to_entry.
      eapply EPI with (cmapd := 0) (cvn := mkCmapv 0 0 0 0); try eassumption.
      all: lazymatch goal with
           | |- wr_at asegs _ _ 120 => first [exact (proj2 FRM) | eassumption]
           | |- wr_at asegs _ _ 16 => exact (proj2 FSH)
           | |- rw_cells asegs _ _ (pix_cells _) => unfold pix_cells; cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data]; exact PXD
           | |- In _ _ => solve [in_live_tac]
           | |- _ \/ _ => left; reflexivity
           | |- _ = 0 -> _ => intros _; reflexivity
           | |- _ <> 0 -> _ => intros NZ; exfalso; exact (NZ CMS0)
           | |- _ <= _ => repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end; lia
           | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
           | |- rt_live _ _ = _ => change (0 =? 0) with true; cbv iota; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity
           | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
           | |- ?g => idtac "LEFT:" g
           end.
    + (* [comment removed for export] *)
      set (cms := p_cmap vs) in *.
      pose proof CMSO as (_ & (INCS & CMS0 & _) & _).
      assert (CMSNZ : cms <> 0) by lia.
      destruct (UCX CMSNZ) as (UCH & TRM). clear UCX.
      pose proof (live_apart2 RT AF Σ m cms 24 pixd 64 ART0 INCS PDIN ltac:(intros E; inversion E)) as DCP.
      assert (CMSPF : forall a, cms <= a < cms + 24 -> PF a).
      { intros a Ha. split; [right; right; left; exists cms, 24; split; [exact INCS| exact Ha]| cbn [outside]; split; [lia| exact I]]. }
      hide CMSO. hide CMSPF.
      chunk_facts RT AF GP cms 24.
      Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x935d8].
      ccm_resync RT AF GP AGF PFS NFA.
      Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x99d38; 0x93618].
      cwalk [0x99d38; 0x93618].
      ccm_resync RT AF GP AGF PFS NFA.
      Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x99d38; 0x995fc; 0x99320; 0x912bc; 0x9382c].
      cwalk [0x99d38; 0x995fc; 0x99320; 0x912bc; 0x9382c].
      (* [comment removed for export] *)
      split_last_CB FRM [24%nat; 4%nat; 4%nat]. split_at FRM 6%nat FRV. split_at FRV 1%nat FRT.
      destruct (cb4_c4' _ _ _ FRV) as (xv & PVC). clear FRV.
      pose proof FSH as SHV. split_at SHV 14%nat SHV2. split_at SHV2 1%nat SHV3. clear SHV SHV3.
      at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                    ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                          repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
      unfold hid in CMSO, CMSPF.
      lazymatch type of AGF with agree_on _ _ ?mc =>
        assert (CMSO1 : cmap_obj (rt_live RT Σ) mc cms cvs) by (exact (cmap_obj_agree (rt_live RT Σ) PF m mc cms cvs CMSO AGF CMSPF)) end.
      hide CMSO. hide CMSPF.
      eapply cps_seq.
      { eapply IV with (lo := lo) (cmap := cms) (pv := fr + 112) (cv := cvs) (x := xv); rt_side idtac.
        all: lazymatch goal with
             | |- cmap_obj _ _ _ _ => repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact CMSO1
             | |- optrV _ _ _ _ _ =>
                 left; unfold optrF, parked in *; split;
                 [ exists fr, 1%nat; rewrite FRS; change (fs_size 1) with 128;
                   split; [left; reflexivity|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
                   split; [lia|]; split; [lia|];
                   replace (shad (fr + 112)) with (fr / 8 + 2147450894) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
                   destruct SHV2 as [[_ B] _]; exact B
                 | unfold SEGTOP_A; repeat split; first [lia | clear - FR64; Z.div_mod_to_equations; lia] ]
             | |- lenv _ _ _ _ _ _ => lenv_tac
             | |- lres _ _ _ _ _ => lres_tac
             | |- ?g => idtac "LEFT:" g
             end. }
      clear SHV2 CMSO1.
      after_call RT AF.
      fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]|
                                      cbn [outside]; destruct (NFA _ Hx) as [N1 N2]; split; [lia| exact I]]).
      refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
      Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x99d38; 0x995fc; 0x99320; 0x912bc; 0x9382c].
      cwalk [0x99d38; 0x995fc; 0x99320; 0x912bc; 0x9382c].
      (* [comment removed for export] *)
      pose proof FR as FRrec. split_at FRrec 12%nat FRrec2. split_at FRrec2 2%nat FRrest. clear FRrec FRrest.
      at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                    ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                          repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
      unfold hid in CMSO, CMSPF.
      lazymatch type of AGF with agree_on _ _ ?mc =>
        assert (CMSO1 : cmap_obj (rt_live RT Σ) mc cms cvs) by (exact (cmap_obj_agree (rt_live RT Σ) PF m mc cms cvs CMSO AGF CMSPF)) end.
      hide CMSO. hide CMSPF.
      assert (RALO : 4096 <= bv_unsigned ra).
      { pose proof traces_ra_lo' as TLO. rewrite Forall_forall in TLO. specialize (TLO _ TRM).
        apply Forall_inv_tail in TLO. apply Forall_inv in TLO. exact TLO. }
      eapply cps_seq.
      { eapply CC with (lo := lo) (cmaps := cms) (cvs := cvs) (ra1 := bv_unsigned ra) (ras := ras); rt_side idtac.
        all: lazymatch goal with
             | |- cmap_obj _ _ _ _ => repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact CMSO1
             | |- uctx _ _ _ _ =>
                 unfold uctx; rewrite ?unsigned_lit by ul;
                 apply (chain_ok_push _ (usp + -112) usp (bv_unsigned ra) (bv_unsigned s0) ras);
                   [ lia | clear - SPA; Z.div_mod_to_equations; lia | ul | lia | lia
                   | rewrite !Z_to_bv_bv_unsigned; exact FRrec2 | ];
                 apply (chain_ok_keep ras m _ usp (bv_unsigned s0) UCH);
                 eapply agree_sub; [exact AGF|]; intros zx Hzx; split; [left; exact Hzx| cbn [outside]; unfold parked in *; split; [lia| exact I]]
             | |- In _ CLIENT_TRACES => exact TRM
             | |- lenv _ _ _ _ _ _ => lenv_tac
             | |- lres _ _ _ _ _ => lres_tac
             | |- ?g => idtac "LEFT:" g
             end. }
      clear CMSO1 FRrec2.
      after_call RT AF.
      fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]| exact I]).
      lazymatch goal with H : cmap_obj _ _ ?p ?cv |- _ => rename H into CMDO; set (cmapd := p) in *; set (cvn := cv) in * end.
      lazymatch goal with H : rt_live RT _ = (c_arr cvn, _) :: _ |- _ => rename H into LVN end.
      lazymatch goal with H : c_depth cvn = _ |- _ => rename H into CDEQ end.
      pose proof CMDO as ((padd & CMDC) & (INCD & CD0 & CD16 & _) & (INAD & AD0 & AD16 & ADN) & CMOKD & NEQD).
      set (ard := c_arr cvn) in *. set (nad := 4 * c_nalloc cvn) in *.
      (* [comment removed for export] *)
      lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ =>
        assert (SUBC : forall e, In e (rt_live RT Σ) -> In e (rt_live RT S) /\ fst e <> cmapd)
          by (intros e He; split; [rewrite LVN; right; right; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact He|];
              apply (fresh_chunk_ne RT AF S mm [(ard, nad)] cmapd 24 _ e A LVN);
              [ cbn [app]; right; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact He | lia | destruct e as [eq ek]; exact (LVP eq ek He) ]);
        assert (SUBA : forall e, In e (rt_live RT Σ) -> In e (rt_live RT S) /\ fst e <> ard)
          by (intros e He; split; [rewrite LVN; right; right; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact He|];
              apply (fresh_chunk_ne RT AF S mm [] ard nad _ e A LVN);
              [ cbn [app]; right; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact He | lia | destruct e as [eq ek]; exact (LVP eq ek He) ]);
        assert (NCMD : forall a, PF a -> a < cmapd \/ cmapd + 24 <= a)
          by (intros a Ha; apply (inner_chunk_apart RT AF S mm cmapd 24 (rt_live RT Σ) (rt_frames RT Σ) usp a A INCD SUBC);
              [ solve [frames_sub_tac] | repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul | exact (proj1 Ha) ]);
        assert (NARD : forall a, PF a -> a < ard \/ ard + nad <= a)
          by (intros a Ha; apply (inner_chunk_apart RT AF S mm ard nad (rt_live RT Σ) (rt_frames RT Σ) usp a A INAD SUBA);
              [ solve [frames_sub_tac] | repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul | exact (proj1 Ha) ]);
        pose proof (live_apart2 RT AF S mm cmapd 24 pixd 64 A INCD ltac:(solve [in_live_tac]) ltac:(intros E; inversion E)) as DCD end.
      chunk_facts RT AF GP cmapd 24.
      lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ =>
        assert (FRSn : rt_frames RT S = (fr, 1%nat) :: rt_frames RT Σ)
          by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity) end.
      fframe_chunk RT AF fr 1%nat 128 cmapd 24.
      unfold cmap_cells in CMDC.
      hide CMDO. hide SUBC. hide SUBA.
      refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
      Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x99d38; 0x995fc; 0x99320; 0x912bc; 0x9382c; 0x93664].
      ccm_resync RT AF GP AGF PFS NFA.
      Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x99d38; 0x93694].
      cwalk [0x99d38; 0x93694].
      ccm_resync RT AF GP AGF PFS NFA.
      Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x93698].
      lstep.
      shbr0_keep.
      ccm_resync RT AF GP AGF PFS NFA.
      Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16); (pixd + 48, pixd + 56)] [0x99d38; 0x995fc; 0x99320; 0x912bc; 0x9382c].
      (* [comment removed for export] *)
      split_at FRM 6%nat FRM2. split_last_CB FRM [24%nat; 4%nat; 12%nat]. split_at FRM 6%nat FRW. split_at FRW 1%nat FRW2.
      destruct (cb4_c4' _ _ _ FRW) as (xw & PWC). clear FRW.
      pose proof FSH as SHW. split_at SHW 8%nat SHW2. split_at SHW2 1%nat SHW3. clear SHW SHW3.
      at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac|
                            split; [intros zz Hzz; right; right; left; exists pixd, 64; split; [solve [in_live_tac]| lia]| exact I]]]])
                    ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; destruct Hx as [_ HxO];
                          cbn [outside] in HxO; unfold shad, SHB in *; repeat split; try exact I; first [lia | tauto | Z.div_mod_to_equations; lia]).
      lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ =>
        assert (CMDO2 : cmap_obj (rt_live RT S) mm cmapd cvn)
          by (split; [exists padd; unfold cmap_cells; exact CMDC|];
              split; [split; [exact INCD| split; [exact CD0| split; [exact CD16| lia]]]|];
              split; [split; [exact INAD| split; [exact AD0| split; [exact AD16| exact ADN]]]|];
              split; [exact CMOKD| exact NEQD]) end.
      eapply cps_seq.
      { eapply IV with (lo := lo) (cmap := cmapd) (pv := fr + 64) (cv := cvn) (x := xw); rt_side idtac.
        all: lazymatch goal with
             | |- cmap_obj _ _ _ _ => exact CMDO2
             | |- optrV _ _ _ _ _ =>
                 left; unfold optrF, parked in *; split;
                 [ exists fr, 1%nat; rewrite FRSn; change (fs_size 1) with 128;
                   split; [left; reflexivity|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
                   split; [lia|]; split; [lia|];
                   replace (shad (fr + 64)) with (fr / 8 + 2147450888) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
                   destruct SHW2 as [[_ B] _]; exact B
                 | unfold SEGTOP_A; repeat split; first [lia | clear - FR64; Z.div_mod_to_equations; lia] ]
             | |- lenv _ _ _ _ _ _ => lenv_tac
             | |- lres _ _ _ _ _ => lres_tac
             | |- ?g => idtac "LEFT:" g
             end. }
      clear SHW2 CMDO2.
      after_call RT AF.
      fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [solve [live_add_tac]| solve [frames_sub_tac]| lia]|
                                      cbn [outside]; destruct (NFA _ Hx) as [N1 N2]; split; [lia| exact I]]).
      refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
      Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x99d38; 0x995fc; 0x99320; 0x912bc; 0x9382c].
      cwalk [0x99d38; 0x995fc; 0x99320; 0x912bc; 0x9382c].
      cps_stop.
      art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
      lazymatch goal with MUx : munch _ ?mm _ |- _ =>
        agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                           repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
      lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ =>
        assert (CMDO3 : cmap_obj (rt_live RT S) mm cmapd cvn)
          by (split; [exists padd; unfold cmap_cells; exact CMDC|];
              split; [split; [solve [in_live_tac]| split; [exact CD0| split; [exact CD16| lia]]]|];
              split; [split; [solve [in_live_tac]| split; [exact AD0| split; [exact AD16| exact ADN]]]|];
              split; [exact CMOKD| exact NEQD]) end.
      to_entry.
      eapply EPI with (cmapd := cmapd) (cvn := cvn); try eassumption.
      all: lazymatch goal with
           | |- wr_at asegs ?mc _ 120 =>
               unfold hid in WRF0; lazymatch type of WRF0 with wr_at asegs ?m0 _ _ =>
                 lazymatch goal with WMx : wmono asegs m0 mc |- _ => exact (wr_at_transport asegs m0 mc _ _ WRF0 WMx) end end
           | |- wr_at asegs _ _ 16 => exact (proj2 FSH)
           | |- rw_cells asegs _ _ (pix_cells _) => unfold pix_cells; cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data]; exact PXD
           | |- In _ _ => solve [in_live_tac]
           | |- _ \/ _ => right; split; [exact CMDO3| exact CDEQ]
           | |- _ = 0 -> _ => intros Z0; exfalso; exact (CMSNZ Z0)
           | |- _ <> 0 -> _ => intros _; lia
           | |- _ <= _ => repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end; lia
           | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
           | |- rt_live _ _ = _ => replace (cmapd =? 0) with false by (symmetry; apply Z.eqb_neq; lia); repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity
           | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
           | |- ?g => idtac "LEFT:" g
           end.

Qed.
End CCM.
