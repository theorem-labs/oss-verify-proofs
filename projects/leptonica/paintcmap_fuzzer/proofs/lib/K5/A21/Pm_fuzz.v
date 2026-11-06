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
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.A21 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit Lept_chain Lept_leaf LeptC_leaf Lept_objkit Pm_iface Pm_iface2 Pm_iface3 Pm_iface4 Pm_okit PmF_kit Pm_objkit Pm_walkkit.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
(* [comment removed for export] *)
Local Ltac live_sub_tac ::=
  let e := fresh "e" in let He := fresh "He" in intros e He;
  try solve [destruct He];
  repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H in * end;
  repeat first [ exact He | apply live_remove_sub in He ].

(* [comment removed for export] *)
Lemma tr_deser : Forall (fun r => Forall (fun f => In [f; r; RA_FUZZ_DESER; RA_TOP] CLIENT_TRACES) DESTROY_FREE_RAS) DESER_DESTROY_RAS.
Proof.
  apply Forall_forall. intros r Hr. apply Forall_forall. intros f Hf.
  unfold DESER_DESTROY_RAS in Hr. unfold DESTROY_FREE_RAS in Hf. cbn [In] in Hr, Hf.
  destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; destruct Hf as [<-|[<-|[]]]; vm_compute; tauto.
Qed.
Lemma tr_destroy : Forall (fun r => Forall (fun f => In [f; r; RA_TOP] CLIENT_TRACES) DESTROY_FREE_RAS) PM_FUZZ_DESTROY_RAS.
Proof.
  apply Forall_forall. intros r Hr. apply Forall_forall. intros f Hf.
  unfold PM_FUZZ_DESTROY_RAS in Hr. unfold DESTROY_FREE_RAS in Hf. cbn [In] in Hr, Hf.
  destruct Hr as [<-|[<-|[<-|[]]]]; destruct Hf as [<-|[<-|[]]]; vm_compute; tauto.
Qed.

(* [comment removed for export] *)
Ltac frame_release_raw RT AF GP MST Σ0 fr k SZ PF AGF PFS usp lo pcafter ivt pft getacl C1 C2 C3 C4 :=
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
    let SSPs := fresh "SSPs" in
    let D1 := fresh "D1" in let D2 := fresh "D2" in let D3 := fresh "D3" in let D4 := fresh "D4" in
    pose proof C1 as D1; hide D1; pose proof C2 as D2; hide D2; pose proof C3 as D3; hide D3; pose proof C4 as D4; hide D4;
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
      unfold hid in SSPs, D1, D2, D3, D4;
      let SSP2 := fresh "SSP" in
      let E1 := fresh "LSEV" in let E2 := fresh "LALLOC" in let E3 := fresh "LDEALLOC" in let E4 := fresh "LHAND" in
      assert (E1 := rw_cells_agree_nw asegs mm m' _ _ D1 (static_agree RT GP client_static mm m' AGS (fun a Ha => Ha) 0xd1840 4 ltac:(cbn; tauto)));
      assert (E2 := rw_cells_agree_nw asegs mm m' _ _ D2 (static_agree RT GP client_static mm m' AGS (fun a Ha => Ha) 0xd1880 8 ltac:(cbn; tauto)));
      assert (E3 := rw_cells_agree_nw asegs mm m' _ _ D3 (static_agree RT GP client_static mm m' AGS (fun a Ha => Ha) 0xd18a0 8 ltac:(cbn; tauto)));
      assert (E4 := rw_cells_agree_nw asegs mm m' _ _ D4 (static_agree RT GP client_static mm m' AGS (fun a Ha => Ha) 0xd1860 8 ltac:(cbn; tauto)));
      clear D1 D2 D3 D4;
      assert (SSP2 : io_ssp m') by (exact (io_ssp_agree RT GP client_static S2 mm m' SSPs ART2 AGS (fun a Ha => Ha)));
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; split; [| exact I]; let Hin := fresh "Hin" in intros Hin;
        lazymatch type of Hx with PF ?z =>
          apply (flag_not_client _ _ (rt_live RT Σ0) (rt_frames RT Σ0) fl lo usp FLN ltac:(lia) ltac:(lia));
          [ first [ solve [live_sub_tac] | solve [live_add_tac] ] | solve [frames_sub_tac] | replace fl with z by lia; getacl Hx ] end);
      apply (cps_ASTA_switch RT _ S2 _ _ _ AL2 AM2);
      clear REL SSPs FLC FLN AGS
    end
  end.

Section PMFUZZ.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis DESER : pixDeserialize_cps RT.
Hypothesis DESTROY : pixDestroy_cps RT.
Hypothesis BOXC : boxCreate_cps RT.
Hypothesis BOXD : boxDestroy_cps RT.
Hypothesis COPY : pixCopy_nn_cps RT.
Hypothesis SEL : pixSetSelectCmap_cps RT.
Hypothesis MSK : pixSetSelectMaskedCmap_cps RT.

Theorem pm_fuzz_ok : pm_fuzz_one_cps RT.
Proof using AF RC GP DESER DESTROY BOXC BOXD COPY SEL MSK.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d bs lo
    FDO MST -> -> -> RATOP DPOS BSL BYTES OWN FR0 LVP LVB CRB S0INV LIBm SSP ART0 MI ST LOW LOR SPT SPA SPB.
  destruct LIBm as ((LSEV & LALLOC & LDEALLOC) & (h0 & LHAND)).
  unfold g_LeptMsgSeverity, g_pix_alloc, g_pix_dealloc, g_stderr_handler in *. clear BYTES.
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, e_pm_fuzz, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold FUZZ_STACK, FUZZ_COST, PM_FUZZ_LIVE, LSTK, STDERR_STACK, RASTER_COST in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  pose proof ST as (STa & STb & _).
  set (PF := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a /\ outside Lept_iface.LIB_FP a).
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a [Ha _]. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]. }
  assert (AL : usp mod 32 = 0 \/ usp mod 32 = 16) by (Z.div_mod_to_equations; lia).
  destruct AL as [AL|AL].
  - (* [comment removed for export] *)
    carve_frame 96%nat ST.
    walk_to AF MST [(usp - 96, usp)] [e_stack_malloc 1%nat; e_pixDeserialize; e_pixDestroy; e_boxCreate; e_pixCopy; e_pixSetSelectCmap; e_boxDestroy; e_pixSetSelectMaskedCmap; 0x8d7a8].
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
    eapply cps_seq.
    { pose proof (gp_stack_malloc_1 RT GP) as SM0; unfold stack_malloc_contract' in SM0; eapply SM0 with (lo := lo); rt_side idtac. }
    after_call RT AF.
    fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]).
    fframe_open RT AF PF (rt_live RT Σ) usp 1%nat 128 ltac:(fun Ha => exact (proj1 Ha)).
    refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
    destruct (Z_lt_ge_dec (Z.of_nat (length bs)) 3) as [SZ|SZ].
    + (* [comment removed for export] *)
      walk_to AF MST [(usp - 96, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_stack_malloc 1%nat; e_pixDeserialize; e_pixDestroy; e_boxCreate; e_pixCopy; e_pixSetSelectCmap; e_boxDestroy; e_pixSetSelectMaskedCmap; 0x8d7a8].
      frame_release_raw RT AF GP MST Σ fr 1%nat 128 PF AGF PFS usp lo 0x8d7b0
        ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
        ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                          repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia])
        ltac:(fun Hx => exact (proj1 Hx)) LSEV LALLOC LDEALLOC LHAND.
      refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
      walk_to AF MST [(usp - 96, usp)] (@nil Z).
      try (lazymatch goal with ST' : stk asegs _ lo (usp + -96) |- _ => release_frame FR ST' usp end).   (* [comment removed for export] *)
      cps_stop.
      apply cps_finish; intros c Hc; subst QF; cbv beta.
      lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S end.
      split; [| alg_tac].
      eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-; eexists.
      split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
      split; [split; [assumption| split; assumption]|].
      split; [intros a Ha Ho; exact (AGF a (conj Ha Ho))|].
      unfold LIB, LIB0, g_LeptMsgSeverity, g_pix_alloc, g_pix_dealloc, g_stderr_handler.
      split; [split; [assumption| split; assumption]| exists h0; assumption].
    + (* [comment removed for export] *)
      walk_to AF MST [(usp - 96, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16); (858208, 858216)]
                   [e_stack_malloc 1%nat; e_pixDeserialize; e_pixDestroy; e_boxCreate; e_pixCopy; e_pixSetSelectCmap; e_boxDestroy; e_pixSetSelectMaskedCmap; 0x8d7a8].
      destruct OWN as [(p0 & n0 & OIN & OLO & OHI & DAL)| ->]; [| cbn [length] in SZ; lia].
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (LH : LIBH mm)
        by (unfold LIBH, LIB0, g_LeptMsgSeverity, g_pix_alloc, g_pix_dealloc, g_stderr_handler, e_devnull; split; [split; [|split]|]; assumption) end.
      clear LSEV LALLOC LDEALLOC LHAND.
      pose proof FR as FRrec. split_before FRrec (C8 s0) FRrec2. clear FRrec.
      at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| split; [intros zz Hzz; static_tac | exact I]]]])
                    ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; destruct Hx as [_ HxO];
                          unfold Lept_iface.LIB_FP, g_stderr_handler in HxO; cbn [outside] in HxO; unfold shad, SHB in *;
                          repeat split; try exact I; first [lia | tauto | Z.div_mod_to_equations; lia]).
      pose proof DESER as DS. unfold pixDeserialize_cps in DS.
      eapply cps_seq.
      { eapply DS with (lo := lo) (dp := d) (n := Z.of_nat (length bs)) (ras := [RA_TOP]); rt_side idtac.
        - right. split; [exact DAL|]. exists p0, n0. repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end. split; [exact OIN | lia].
        - unfold uctx. (rewrite !unsigned_lit by lia). unfold parked in S0INV.
          (apply chain_ok_push with (fp1 := bv_unsigned s0)).
          + lia.
          + (clear - SPA; Z.div_mod_to_equations; lia).
          + (unfold USTACK_TOP; lia).
          + (unfold RA_TOP; lia).
          + (apply bv_unsigned_in_range).
          + (rewrite Z_to_bv_bv_unsigned; rewrite <- RATOP; rewrite Z_to_bv_bv_unsigned).
            (lazymatch type of FRrec2 with rw_cells _ _ ?a _ => replace (usp + -16) with a by lia end). (exact FRrec2).
          + (cbn [chain_ok]; unfold link_invalid; lia).
        - (exact tr_deser).
        - lenv_tac.
        - unfold RASTER_COST. lres_tac. }
      after_call RT AF.
      fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]| exact I]).
      lazymatch goal with H : ?p = 0 \/ _ |- _ => rename H into POBJ; set (pix := p) in * end.
      lazymatch goal with H : pix = 0 -> rt_live RT _ = _ |- _ => rename H into LVZ end.
      lazymatch goal with H : pix <> 0 -> live_destroy _ _ _ _ = _ |- _ => rename H into LVD end.
      match goal with H : forall p n, In (p, n) (rt_live RT ?S) -> 0 < n |- _ => lazymatch S with Σ => fail | _ => rename H into LVP1 end end.
      match goal with H : Z.of_nat (length (rt_live RT _)) <= Z.of_nat (length (rt_live RT _)) + 4 |- _ => rename H into LEN1 end.
      match goal with H : rt_credit RT _ - _ <= rt_credit RT _ |- _ => rename H into CR1 end.
      destruct (Z.eq_dec pix 0) as [PZ|PNZ].
      * (* [comment removed for export] *)
        clear POBJ LVD. pose proof (LVZ PZ) as LVE. clear LVZ. rewrite PZ in *.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
        walk_to AF MST [(usp - 96, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_stack_malloc 1%nat; e_pixDeserialize; e_pixDestroy; e_boxCreate; e_pixCopy; e_pixSetSelectCmap; e_boxDestroy; e_pixSetSelectMaskedCmap; 0x8d7a8].
        frame_release_g RT AF GP MST Σ fr 1%nat 128 PF AGF PFS usp lo 0x8d7b0
          ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
          ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                            repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia])
          ltac:(fun Hx => exact (proj1 Hx)) ltac:(fun fl FLN => idtac).
        refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
        walk_to AF MST [(usp - 96, usp)] (@nil Z).
        try (lazymatch goal with ST' : stk asegs _ lo (usp + -96) |- _ => release_frame FR ST' usp end).   (* [comment removed for export] *)
        cps_stop.
        apply cps_finish; intros c Hc; subst QF; cbv beta.
        lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S end.
        split; [| unfold RASTER_COST in *; alg_tac].
        eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-; eexists.
        split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
        split; [split; [assumption| split; assumption]|].
        split; [intros a Ha Ho; exact (AGF a (conj Ha Ho))|].
        lazymatch goal with LHx : LIBH ?mm |- LIB ?mm => destruct LHx as (LH0 & LHH); split; [exact LH0| eexists; exact LHH] end.
      * (* [comment removed for export] *)
        destruct POBJ as [PZ|(POBJ & VDATA)]; [contradiction|]. clear LVZ. pose proof (LVD PNZ) as LVE. clear LVD.
        lazymatch type of POBJ with pix_obj _ _ _ ?vv ?cc => set (v := vv) in *; set (cv := cc) in * end.
        pose proof POBJ as (PXC & (PIN & PX0 & PX16 & _) & _). clear PXC.
        chunk_facts RT AF GP pix 64.
        lazymatch type of PIN with In _ (rt_live RT ?S1) =>
          assert (SUB01 : forall e, In e (rt_live RT Σ) -> In e (rt_live RT S1))
            by (intros e He; apply (live_destroy_sub pix v cv); rewrite LVE; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact He) end.
        lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ =>
          assert (FRSh : rt_frames RT S = (fr, 1%nat) :: rt_frames RT Σ)
            by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity) end.
        hide POBJ.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
        (* [comment removed for export] *)
        Time walk_to AF MST [(usp - 96, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_stack_malloc 1%nat; e_pixDeserialize; e_pixDestroy; e_boxCreate; e_pixCopy; e_pixSetSelectCmap; e_boxDestroy; e_pixSetSelectMaskedCmap; 0x8d7a8].
        unfold hid in POBJ.
        lazymatch goal with A : ART RT ?S ?m0, MUx : munch _ ?m0 ?m1 |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
          assert (KL1 : keeps_live (rt_live RT S) m0 m1)
            by (apply (keeps_live_walk1 RT AF S m0 m1 fr usp (usp + -96) A ltac:(rewrite FRSh; left; reflexivity)
                         ltac:(repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; unfold STACK_WIN; lia) MUx));
          pose proof (pix_obj_keep _ m0 m1 pix v cv KL1 POBJ) as POBJ1; clear KL1 end.
        clear POBJ.
        at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                            repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
        pose proof BOXC as BC. unfold boxCreate_cps in BC.
        eapply cps_seq.
        { eapply BC with (lo := lo) (x := 278) (y := 35) (w := 122) (h := 50); rt_side idtac.
          all: lazymatch goal with
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- lres _ _ _ _ _ =>
                   unfold lres, RASTER_COST, FRAMES_MAX, LIVE_MAX in *; rewrite FRSh, FR0; cbn [length];
                   repeat match goal with H : rt_live RT _ = rt_live RT _ |- _ => rewrite H in * end;
                   repeat match goal with H : rt_credit RT _ = _ |- _ => rewrite H in * end;
                   split; [lia| split; [lia| split; [lia| exact LVP1]]]
               | |- ?g => idtac "LEFT-BOXC:" g
               end. }
        after_call RT AF.
        lazymatch goal with H : box_obj _ _ ?bb 278 35 122 50 |- _ => rename H into BOBJ; set (b := bb) in * end.
        lazymatch goal with H : rt_live RT _ = (b, 20) :: _ |- _ => rename H into LV2 end.
        lazymatch goal with AGx : agree_on _ ?ma ?mb |- cps _ (ASTA RT _ _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
          assert (KL2 : keeps_live (rt_live RT _) ma mb) by (eapply keeps_live_of_agree; [exact AGx| intros e He; exact He| intros; exact I]);
          pose proof (pix_obj_keep _ ma mb pix v cv KL2 POBJ1) as POBJ2; clear KL2 POBJ1 end.
        fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [exact SUB01| solve [frames_sub_tac]| lia]| exact I]).
        lazymatch goal with A : ART RT ?S2 ?mm |- cps _ (ASTA RT ?S2 _ _) _ =>
          assert (FRS2 : rt_frames RT S2 = (fr, 1%nat) :: rt_frames RT Σ)
            by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity);
          assert (LVP2 : forall p n, In (p, n) (rt_live RT S2) -> 0 < n)
            by (intros p n Hin; rewrite LV2 in Hin; destruct Hin as [E|Hin]; [injection E as <- <-; lia| exact (LVP1 p n Hin)]) end.
        hide POBJ2. hide BOBJ.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
        (* [comment removed for export] *)
        Time walk_to AF MST [(usp - 96, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_stack_malloc 1%nat; e_pixDeserialize; e_pixDestroy; e_boxCreate; e_pixCopy; e_pixSetSelectCmap; e_boxDestroy; e_pixSetSelectMaskedCmap; 0x8d7a8].
        unfold hid in POBJ2, BOBJ.
        lazymatch goal with A : ART RT ?S ?m0, MUx : munch _ ?m0 ?m1 |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
          assert (KL3 : keeps_live (rt_live RT S) m0 m1)
            by (apply (keeps_live_walk1 RT AF S m0 m1 fr usp (usp + -96) A ltac:(rewrite FRS2; left; reflexivity)
                         ltac:(repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; unfold STACK_WIN; lia) MUx));
          pose proof (pix_obj_keep _ m0 m1 pix v cv (keeps_live_sub (rt_live RT S) _ m0 m1 KL3 ltac:(intros e He; rewrite LV2; right; exact He)) POBJ2) as POBJ3;
          pose proof (box_obj_keep _ m0 m1 b 278 35 122 50 BOBJ (keeps_live_sub (rt_live RT S) [(b, 20)] m0 m1 KL3 ltac:(intros e [<-|[]]; rewrite LV2; left; reflexivity))) as BOBJ3;
          clear KL3 end.
        clear POBJ2 BOBJ.
        at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                            repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
        pose proof COPY as CP. unfold pixCopy_nn_cps in CP.
        eapply cps_seq.
        { eapply CP with (lo := lo) (pixs := pix) (v := v) (cv := cv); rt_side idtac.
          all: lazymatch goal with
               | |- pix_obj ?lv _ _ _ _ => apply (pix_obj_mono _ lv _ _ _ _ ltac:(intros e He; rewrite LV2; right; exact He) POBJ3)
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- lres _ _ _ _ _ =>
                   unfold lres, RASTER_COST, FRAMES_MAX, LIVE_MAX in *; rewrite FRS2, FR0, LV2; cbn [length];
                   repeat match goal with H : rt_live RT _ = rt_live RT _ |- _ => rewrite H in * end;
                   repeat match goal with H : rt_credit RT _ = _ |- _ => rewrite H in * end;
                   split; [lia| split; [lia| split; [lia| rewrite <- LV2; exact LVP2]]]
               | |- ?g => idtac "LEFT-COPY1:" g
               end. }
        after_call RT AF.
        (* [comment removed for export] *)
        lazymatch goal with HC : pm_hdr_copy _ ?vv _ ?cc |- _ =>
          lazymatch goal with H : pix_obj _ _ ?p vv cc |- _ => rename H into POBJC; rename HC into HC1; set (p1 := p) in *; set (v1 := vv) in *; set (cv1 := cc) in * end end.
        lazymatch goal with H : p1 <> 0 |- _ => rename H into P1NZ end.
        lazymatch goal with H : rt_live RT _ = pm_copy_live p1 v1 cv1 _ |- _ => rename H into LV3 end.
        assert (VD1 : p_data v1 <> 0) by (destruct HC1 as (_ & _ & _ & _ & X & _); exact X).
        rewrite pm_copy_live_app in LV3.
        lazymatch goal with AGx : agree_on (fun a => aclient ?lv _ _ a /\ _) ?ma ?mb |- cps _ (ASTA RT _ _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
          assert (KL4 : keeps_live lv ma mb) by (eapply keeps_live_of_agree; [exact AGx| intros e He; exact He| intros; exact I]);
          pose proof (pix_obj_keep _ ma mb pix v cv (keeps_live_sub lv _ ma mb KL4 ltac:(intros e He; rewrite LV2; right; exact He)) POBJ3) as POBJ4;
          pose proof (box_obj_keep _ ma mb b 278 35 122 50 BOBJ3 (keeps_live_sub lv [(b, 20)] ma mb KL4 ltac:(intros e [<-|[]]; rewrite LV2; left; reflexivity))) as BOBJ4;
          clear KL4 POBJ3 BOBJ3 end.
        fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; rewrite LV2; right; exact (SUB01 e He)| solve [frames_sub_tac]| lia]| exact I]).
        lazymatch goal with A : ART RT ?S3 ?mm |- cps _ (ASTA RT ?S3 _ _) _ =>
          assert (FRS3 : rt_frames RT S3 = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity);
          assert (LVP3 : forall p n, In (p, n) (rt_live RT S3) -> 0 < n)
            by (intros p n Hin; rewrite LV3 in Hin; apply in_app_or in Hin; destruct Hin as [Hin|Hin]; [exact (pm_copy_new_pos _ _ _ _ _ POBJC VD1 p n Hin)| exact (LVP2 p n Hin)]);
          assert (SUB23 : forall e, In e (rt_live RT _) -> In e (rt_live RT S3)) by (intros e He; rewrite LV3; apply in_or_app; right; exact He);
          assert (LEN3 : Z.of_nat (length (rt_live RT S3)) <= Z.of_nat (length (rt_live RT Σ)) + 9)
            by (rewrite LV3, length_app, LV2; cbn [length]; pose proof (pm_copy_new_len p1 v1 cv1);
                repeat match goal with H : rt_live RT _ = rt_live RT _ |- _ => rewrite H in * end; lia);
          assert (NEB : b <> p1)
            by (pose proof (live_apart_app RT AF S3 mm _ _ p1 64 b 20 A LV3 ltac:(unfold pm_copy_new; apply in_or_app; right; right; left; reflexivity) ltac:(rewrite LV2; left; reflexivity)); lia)
        end.
        park LV3. hide POBJ4. hide BOBJ4. hide POBJC. hide NEB.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
        (* [comment removed for export] *)
        Time walk_to AF MST [(usp - 96, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_stack_malloc 1%nat; e_pixDeserialize; e_pixDestroy; e_boxCreate; e_pixCopy; e_pixSetSelectCmap; e_boxDestroy; e_pixSetSelectMaskedCmap; 0x8d7a8].
        unfold hid in POBJ4, BOBJ4, POBJC, NEB.
        lazymatch goal with A : ART RT ?S ?m0, MUx : munch _ ?m0 ?m1 |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
          assert (KL5 : keeps_live (rt_live RT S) m0 m1)
            by (apply (keeps_live_walk1 RT AF S m0 m1 fr usp (usp + -96) A ltac:(rewrite FRS3; left; reflexivity)
                         ltac:(repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; unfold STACK_WIN; lia) MUx));
          pose proof (pix_obj_keep _ m0 m1 pix v cv (keeps_live_sub (rt_live RT S) _ m0 m1 KL5 ltac:(intros e He; apply SUB23; rewrite LV2; right; exact He)) POBJ4) as POBJ5;
          pose proof (box_obj_keep _ m0 m1 b 278 35 122 50 BOBJ4 (keeps_live_sub (rt_live RT S) [(b, 20)] m0 m1 KL5 ltac:(intros e [<-|[]]; apply SUB23; rewrite LV2; left; reflexivity))) as BOBJ5;
          pose proof (pix_obj_keep _ m0 m1 p1 v1 cv1 KL5 POBJC) as POBJC5; clear KL5 end.
        clear POBJ4 BOBJ4 POBJC.
        at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                            repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
        pose proof SEL as SL. unfold pixSetSelectCmap_cps in SL.
        eapply cps_seq.
        { eapply SL with (lo := lo) (pix := p1) (b := b) (v := v1) (cv := cv1); rt_side idtac.
          all: lazymatch goal with
               | |- box_obj ?lv _ _ _ _ _ _ => exact (box_obj_mono _ lv _ _ _ _ _ _ SUB23 BOBJ5)
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- lres _ _ _ _ _ =>
                   unfold lres, RASTER_COST, FRAMES_MAX, LIVE_MAX in *; rewrite FRS3, FR0; cbn [length];
                   repeat match goal with H : rt_credit RT _ = _ |- _ => rewrite H in * end;
                   split; [lia| split; [lia| split; [lia| exact LVP3]]]
               | |- ?g => idtac "LEFT-SEL:" g
               end. }
        (* [comment removed for export] *)
        lazymatch type of LVE with live_destroy _ _ _ (rt_live RT ?S) = _ => rename S into S1 end.
        lazymatch type of LV2 with rt_live RT ?S = _ => rename S into S2 end.
        lazymatch type of LV3 with parked (rt_live RT ?S = _) => rename S into S3 end.
        (* [comment removed for export] *)
        cps_open RT. after_call_unfold. fold_zdefs. unfold rt_after, rt_after_f in *. split_hyps.
        unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *.
        repeat match goal with H : context [bv_unsigned (Z_to_bv 64 ?e)] |- _ => rewrite (unsigned_lit e) in H by lia end.
        lazymatch goal with P : rt_pres_fp (rt_live RT ?S4) (rt_frames RT ?S3) ?spc (pm_fp v1 cv1) ?ma ?mb, E4 : rt_live RT ?S4 = rt_live RT ?S3 |- _ =>
          assert (AG : agree_on (aclient (rt_live RT S2) (rt_frames RT S3) spc) ma mb)
            by (intros a Ha; apply P;
                [ apply (aclient_mono _ _ _ _ _ _ _ Ha); [rewrite E4; exact SUB23| intros e He; exact He| lia]
                | unfold parked in LV3;
                  exact (tail_client_outside RT AF S3 ma (pm_copy_new p1 v1 cv1) (rt_live RT S2) (rt_live RT S2) (rt_frames RT S3) spc _ (pm_fp v1 cv1)
                           ARTc3 LV3 (pm_fp_in_new p1 v1 cv1) (fun e He => He) (fun e He => He)
                           ltac:(repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; unfold STACK_WIN; lia) Ha) ]);
          clear P
        end.
        Time lazymatch goal with AGx : agree_on (aclient (rt_live RT S2) _ _) ?ma ?mb |- _ => rt_transport ma mb AGx ltac:(fun A => acl_dispatch A) end.
        fix_ret_pc.
        lazymatch goal with AGx : agree_on (aclient (rt_live RT S2) _ _) ?ma ?mb |- _ =>
          pose proof (keeps_live_of_agf _ _ _ ma mb AGx) as KL6;
          pose proof (pix_obj_keep _ ma mb pix v cv (keeps_live_sub _ _ ma mb KL6 ltac:(intros e He; rewrite LV2; right; exact He)) POBJ5) as POBJ6;
          pose proof (box_obj_keep _ ma mb b 278 35 122 50 BOBJ5 (keeps_live_sub _ [(b, 20)] ma mb KL6 ltac:(intros e [<-|[]]; rewrite LV2; left; reflexivity))) as BOBJ6;
          clear KL6 POBJ5 BOBJ5 POBJC5 end.
        fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; rewrite LV2; right; exact (SUB01 e He)| solve [frames_sub_tac]| lia]).
        lazymatch goal with H : rt_live RT ?S = rt_live RT S3 |- _ => rename S into S4; rename H into LV4 end.
        lazymatch goal with |- cps _ (ASTA RT S4 _ (eq (MS _ _ _ _ _ ?mm _))) _ => rename mm into m5 end.
        lazymatch goal with H : pix_obj (rt_live RT S4) m5 p1 v1 ?c |- _ => rename H into POBJC6; set (cv1' := c) in * end.
        lazymatch goal with H : c_arr cv1' = c_arr cv1 |- _ => rename H into CA1 end.
        lazymatch goal with H : c_nalloc cv1' = c_nalloc cv1 |- _ => rename H into CN1 end.
        lazymatch goal with H : rt_credit RT S3 - 4 <= rt_credit RT S4 |- _ => rename H into CR4 end.

        lazymatch goal with A : ART RT S4 ?mm |- cps _ (ASTA RT S4 _ _) _ =>
          assert (FRS4 : rt_frames RT S4 = (fr, 1%nat) :: rt_frames RT Σ)
            by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity);
          assert (LVP4 : forall p n, In (p, n) (rt_live RT S4) -> 0 < n) by (rewrite LV4; exact LVP3) end.
        hide POBJ6. hide BOBJ6. hide POBJC6.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
        (* [comment removed for export] *)
        Time walk_to AF MST [(usp - 96, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_stack_malloc 1%nat; e_pixDeserialize; e_pixDestroy; e_boxCreate; e_pixCopy; e_pixSetSelectCmap; e_boxDestroy; e_pixSetSelectMaskedCmap; 0x8d7a8].
        unfold hid in POBJ6, BOBJ6, POBJC6.
        lazymatch goal with A : ART RT ?S ?m0, MUx : munch _ ?m0 ?m1 |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
          assert (KL7 : keeps_live (rt_live RT S) m0 m1)
            by (apply (keeps_live_walk1 RT AF S m0 m1 fr usp (usp + -96) A ltac:(rewrite FRS4; left; reflexivity)
                         ltac:(repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; unfold STACK_WIN; lia) MUx));
          pose proof (pix_obj_keep _ m0 m1 pix v cv (keeps_live_sub (rt_live RT S) _ m0 m1 KL7 ltac:(intros e He; rewrite LV4; apply SUB23; rewrite LV2; right; exact He)) POBJ6) as POBJ7;
          pose proof (box_obj_keep _ m0 m1 b 278 35 122 50 BOBJ6 (keeps_live_sub (rt_live RT S) [(b, 20)] m0 m1 KL7 ltac:(intros e [<-|[]]; rewrite LV4; apply SUB23; rewrite LV2; left; reflexivity))) as BOBJ7;
          pose proof (pix_obj_keep _ m0 m1 p1 v1 cv1' KL7 POBJC6) as POBJC7; clear KL7 end.
        clear POBJ6 BOBJ6 POBJC6.
        split_at FRM 6%nat FRMb. split_at FRMb 1%nat FRMc.
        pose proof FSH as SHC. split_at SHC 8%nat SHC8. split_at SHC8 1%nat SHC9. clear SHC SHC9.
        at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                            repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
        pose proof BOXD as BD. unfold boxDestroy_cps in BD.
        eapply cps_seq.
        { eapply BD with (lo := lo) (pp := fr + 64) (b := b) (x := 278) (y := 35) (w := 122) (h := 50); rt_side idtac.
          all: lazymatch goal with
               | |- optrF _ _ _ _ _ =>
                   unfold optrF, own_frame, parked in *; split;
                   [ exists fr, 1%nat; rewrite FRS4; change (fs_size 1) with 128;
                     split; [left; reflexivity|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
                     split; [lia|]; split; [lia|];
                     replace (shad (fr + 64)) with (fr / 8 + 2147450888) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
                     destruct SHC8 as [[_ B] _]; exact B
                   | unfold SEGTOP_A; repeat split; first [lia | clear - FR64; Z.div_mod_to_equations; lia] ]
               | |- rw_cells _ _ _ [C8 _] => exact FRMb
               | |- box_obj ?lv _ _ _ _ _ _ => exact (box_obj_mono _ lv _ _ _ _ _ _ ltac:(intros e He; rewrite LV4; exact (SUB23 e He)) BOBJ7)
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- forall p n, In (p, n) _ -> 0 < n => exact LVP4
               | |- ?g => idtac "LEFT-BD:" g
               end. }
        clear SHC8.
        Time after_call RT AF.
        lazymatch goal with H : rt_live RT ?S = live_remove b (rt_live RT S4) |- _ => rename S into S5; rename H into LV5r end.
        lazymatch goal with |- cps _ (ASTA RT S5 _ (eq (MS _ _ _ _ _ ?mm _))) _ => rename mm into m6 end.
        (* [comment removed for export] *)
        lazymatch goal with A : ART RT S4 m5 |- _ =>
          assert (ND4 : List.NoDup (map fst (pm_copy_live p1 v1 cv1 ((b, 20) :: rt_live RT S1))))
            by (pose proof (live_nodup RT AF S4 m5 A LVP4) as ND; rewrite LV4 in ND; unfold parked in LV3; rewrite LV3, LV2 in ND;
                rewrite pm_copy_live_app; exact ND) end.
        assert (LV5 : rt_live RT S5 = pm_copy_new p1 v1 cv1 ++ rt_live RT S1)
          by (rewrite LV5r, LV4; unfold parked in LV3; rewrite LV3, LV2, <- pm_copy_live_app, (pm_copy_live_remove_box b 20 p1 v1 cv1 _ ND4), pm_copy_live_app; reflexivity).
        lazymatch goal with AGx : agree_on (fun a => aclient (rt_live RT S5) _ _ a /\ outside [(fr + 64, fr + 64 + 8)] a) ?ma ?mb, A5 : ART RT S5 ?mb |- _ =>
          assert (KL8 : keeps_live (rt_live RT S5) ma mb)
            by (eapply keeps_live_of_agree; [exact AGx| intros e He; exact He|];
                intros qq kk xx Hq Hx; cbn [outside]; split; [| exact I];
                exact (chunk_outside_frame RT AF S5 mb fr 1%nat qq kk (fr + 64) (fr + 64 + 8) xx A5
                         ltac:(repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; left; reflexivity)
                         ltac:(lia) ltac:(change (fs_size 1) with 128; lia) Hq Hx));
          pose proof (pix_obj_keep _ ma mb pix v cv (keeps_live_sub _ _ ma mb KL8 ltac:(intros e He; rewrite LV5; apply in_or_app; right; exact He)) POBJ7) as POBJ8;
          pose proof (pix_obj_move _ (rt_live RT S5) ma mb p1 v1 cv1' POBJC7
                        ltac:(intros e He; rewrite LV5; apply in_or_app; left; exact (pix_chunks_new p1 v1 cv1 cv1' CA1 CN1 e He))
                        (keeps_live_sub _ [(p1, 64)] ma mb KL8 ltac:(intros e [<-|[]]; rewrite LV5; apply in_or_app; left;
                                                                     apply (pix_chunks_new p1 v1 cv1 cv1' CA1 CN1); unfold pix_chunks; left; reflexivity))
                        (fun NZ => keeps_live_sub _ [(p_cmap v1, 24)] ma mb KL8 ltac:(intros e [<-|[]]; rewrite LV5; apply in_or_app; left;
                                     apply (pix_chunks_new p1 v1 cv1 cv1' CA1 CN1); unfold pix_chunks; right; apply in_or_app; right;
                                     replace (p_cmap v1 =? 0) with false by (symmetry; apply Z.eqb_neq; exact NZ); left; reflexivity))) as POBJC8;
          clear KL8 end.
        clear POBJ7 BOBJ7 POBJC7.
        fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; rewrite LV5; apply in_or_app; right; exact (SUB01 e He)| solve [frames_sub_tac]| lia]|
                                        cbn [outside]; destruct (NFA _ Hx) as [N1 N2]; split; [lia| exact I]]).
        lazymatch goal with A : ART RT S5 ?mm |- cps _ (ASTA RT S5 _ _) _ =>
          assert (FRS5 : rt_frames RT S5 = (fr, 1%nat) :: rt_frames RT Σ)
            by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity);
          assert (LVP5 : forall p n, In (p, n) (rt_live RT S5) -> 0 < n)
            by (intros p n Hin; rewrite LV5r in Hin; exact (LVP4 p n (live_remove_sub _ _ _ Hin))) end.
        hide POBJ8. hide POBJC8.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
        (* [comment removed for export] *)
        Time walk_to AF MST [(usp - 96, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_stack_malloc 1%nat; e_pixDeserialize; e_pixDestroy; e_boxCreate; e_pixCopy; e_pixSetSelectCmap; e_boxDestroy; e_pixSetSelectMaskedCmap; 0x8d7a8].
        unfold hid in POBJ8, POBJC8.
        lazymatch goal with A : ART RT ?S ?m0, MUx : munch _ ?m0 ?m1 |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
          assert (KL9 : keeps_live (rt_live RT S) m0 m1)
            by (apply (keeps_live_walk1 RT AF S m0 m1 fr usp (usp + -96) A ltac:(rewrite FRS5; left; reflexivity)
                         ltac:(repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; unfold STACK_WIN; lia) MUx));
          pose proof (pix_obj_keep _ m0 m1 pix v cv (keeps_live_sub (rt_live RT S) _ m0 m1 KL9 ltac:(intros e He; rewrite LV5; apply in_or_app; right; exact He)) POBJ8) as POBJ9;
          pose proof (pix_obj_keep _ m0 m1 p1 v1 cv1' KL9 POBJC8) as POBJC9; clear KL9 end.
        clear POBJ8 POBJC8.
        split_at FRMc 1%nat FRMd. split_at FRMd 1%nat FRMe.
        pose proof FSH as SHC. split_at SHC 12%nat SHC12. split_at SHC12 1%nat SHC13. clear SHC SHC13.
        pose proof FR as FRrec. split_before FRrec (C8 s0) FRrec9. clear FRrec.
        at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                            repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
        pose proof DESTROY as DY. unfold pixDestroy_cps in DY.
        eapply cps_seq.
        { eapply DY with (lo := lo) (pp := fr + 96) (pix := p1) (v := v1) (cv := cv1') (ras := [RA_TOP]); rt_side idtac.
          all: lazymatch goal with
               | |- optrL _ _ _ _ _ _ =>
                   unfold optrL, parked in *; split;
                   [ right; exists fr, 1%nat; rewrite FRS5; change (fs_size 1) with 128;
                     split; [left; reflexivity|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
                     split; [lia|]; split; [lia|];
                     replace (shad (fr + 96)) with (fr / 8 + 2147450892) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
                     destruct SHC12 as [[_ B] _]; exact B
                   | unfold SEGTOP_A; repeat split; first [lia | clear - FR64; Z.div_mod_to_equations; lia] ]
               | |- rw_cells _ _ _ [C8 _] => exact FRMd
               | |- pix_obj _ _ _ _ _ => exact POBJC9
               | |- uctx _ _ _ _ =>
                   unfold uctx; rewrite !unsigned_lit by lia; unfold parked in S0INV;
                   apply chain_ok_push with (fp1 := bv_unsigned s0);
                     [ lia | clear - SPA; Z.div_mod_to_equations; lia | unfold USTACK_TOP; lia | unfold RA_TOP; lia | apply bv_unsigned_in_range
                     | rewrite Z_to_bv_bv_unsigned; rewrite <- RATOP; rewrite Z_to_bv_bv_unsigned;
                       lazymatch type of FRrec9 with rw_cells _ _ ?a _ => replace (usp + -16) with a by lia end; exact FRrec9
                     | cbn [chain_ok]; unfold link_invalid; lia ]
               | |- Forall _ _ => pose proof tr_destroy as TD; unfold PM_FUZZ_DESTROY_RAS in TD; exact (Forall_inv TD)
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- lres _ _ _ _ _ =>
                   unfold lres, RASTER_COST, FRAMES_MAX, LIVE_MAX in *; rewrite FRS5, FR0; cbn [length];
                   split; [lia| split; [rewrite LV5, length_app; pose proof (pm_copy_new_len p1 v1 cv1);
                                        repeat match goal with H : rt_live RT _ = rt_live RT _ |- _ => rewrite H in * end; lia|
                   split; [repeat match goal with H : rt_credit RT _ = _ |- _ => rewrite H in * end; lia| exact LVP5]]]
               | |- ?g => idtac "LEFT-DY1:" g
               end. }
        clear SHC12.
        assert (ANZ1 : p_cmap v1 <> 0 -> c_arr cv1 <> 0)
          by (intros NZ; destruct POBJC9 as (_ & _ & _ & _ & [CZ|((_ & _ & (_ & A0 & _) & _) & _)]); [contradiction| rewrite <- CA1; lia]).
        lazymatch goal with A : ART RT S5 ?mm |- _ =>
          assert (ND5 : List.NoDup (map fst (pm_copy_live p1 v1 cv1 (rt_live RT S1))))
            by (pose proof (live_nodup RT AF S5 mm A LVP5) as ND; rewrite LV5 in ND; rewrite pm_copy_live_app; exact ND) end.
        Time after_call RT AF.
        lazymatch goal with H : rt_live RT ?S = live_destroy p1 v1 cv1' (rt_live RT S5) |- _ => rename S into S6; rename H into LV6r end.
        lazymatch goal with |- cps _ (ASTA RT S6 _ (eq (MS _ _ _ _ _ ?mm _))) _ => rename mm into m7 end.
        (* [comment removed for export] *)
        assert (LV6 : rt_live RT S6 = rt_live RT S1)
          by (rewrite LV6r, LV5, <- pm_copy_live_app; exact (pm_copy_roundtrip p1 v1 cv1 cv1' _ ND5 CA1 VD1 ANZ1)).
        lazymatch goal with AGx : agree_on (fun a => aclient (rt_live RT S6) _ _ a /\ outside [(fr + 96, fr + 96 + 8)] a) ?ma ?mb, A6 : ART RT S6 ?mb |- _ =>
          assert (KL10 : keeps_live (rt_live RT S6) ma mb)
            by (eapply keeps_live_of_agree; [exact AGx| intros e He; exact He|];
                intros qq kk xx Hq Hx; cbn [outside]; split; [| exact I];
                exact (chunk_outside_frame RT AF S6 mb fr 1%nat qq kk (fr + 96) (fr + 96 + 8) xx A6
                         ltac:(repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; left; reflexivity)
                         ltac:(lia) ltac:(change (fs_size 1) with 128; lia) Hq Hx));
          pose proof (pix_obj_keep _ ma mb pix v cv (keeps_live_sub _ _ ma mb KL10 ltac:(intros e He; rewrite LV6; exact He)) POBJ9) as POBJ10;
          clear KL10 end.
        clear POBJ9 POBJC9.
        fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; rewrite LV6; exact (SUB01 e He)| solve [frames_sub_tac]| lia]|
                                        cbn [outside]; destruct (NFA _ Hx) as [N1 N2]; split; [lia| exact I]]).
        lazymatch goal with A : ART RT S6 ?mm |- cps _ (ASTA RT S6 _ _) _ =>
          assert (FRS6 : rt_frames RT S6 = (fr, 1%nat) :: rt_frames RT Σ)
            by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity);
          assert (LVP6 : forall p n, In (p, n) (rt_live RT S6) -> 0 < n) by (rewrite LV6; exact LVP1) end.
        clear ND4 ND5 ANZ1 LV5r LV6r.
        hide POBJ10.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
        (* [comment removed for export] *)
        Time walk_to AF MST [(usp - 96, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_stack_malloc 1%nat; e_pixDeserialize; e_pixDestroy; e_boxCreate; e_pixCopy; e_pixSetSelectCmap; e_boxDestroy; e_pixSetSelectMaskedCmap; 0x8d7a8].
        unfold hid in POBJ10.
        lazymatch goal with A : ART RT ?S ?m0, MUx : munch _ ?m0 ?m1 |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
          assert (KL11 : keeps_live (rt_live RT S) m0 m1)
            by (apply (keeps_live_walk1 RT AF S m0 m1 fr usp (usp + -96) A ltac:(rewrite FRS6; left; reflexivity)
                         ltac:(repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; unfold STACK_WIN; lia) MUx));
          pose proof (pix_obj_keep _ m0 m1 pix v cv (keeps_live_sub (rt_live RT S) _ m0 m1 KL11 ltac:(intros e He; rewrite LV6; exact He)) POBJ10) as POBJ11;
          clear KL11 end.
        clear POBJ10.
        at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                            repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
        eapply cps_seq.
        { eapply CP with (lo := lo) (pixs := pix) (v := v) (cv := cv); rt_side idtac.
          all: lazymatch goal with
               | |- pix_obj ?lv _ _ _ _ => apply (pix_obj_mono _ lv _ _ _ _ ltac:(intros e He; rewrite LV6; exact He) POBJ11)
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- lres _ _ _ _ _ =>
                   unfold lres, RASTER_COST, FRAMES_MAX, LIVE_MAX in *; rewrite FRS6, FR0, LV6; cbn [length];
                   repeat match goal with H : rt_live RT _ = rt_live RT _ |- _ => rewrite H in * end;
                   repeat match goal with H : rt_credit RT _ = _ |- _ => rewrite H in * end;
                   split; [lia| split; [lia| split; [lia| exact LVP1]]]
               | |- ?g => idtac "LEFT-COPY2:" g
               end. }
        Time after_call RT AF.
        (* [comment removed for export] *)
        lazymatch goal with HC : pm_hdr_copy v ?vv cv ?cc |- _ =>
          lazymatch goal with H : pix_obj _ _ ?p vv cc |- _ => rename H into POBJC2; rename HC into HC2; set (p2 := p) in *; set (v2 := vv) in *; set (cv2 := cc) in * end end.
        lazymatch goal with H : p2 <> 0 |- _ => rename H into P2NZ end.
        lazymatch goal with H : rt_live RT ?S = pm_copy_live p2 v2 cv2 (rt_live RT S6) |- _ => rename S into S7; rename H into LV7 end.
        lazymatch goal with |- cps _ (ASTA RT S7 _ (eq (MS _ _ _ _ _ ?mm _))) _ => rename mm into m8 end.
        assert (VD2 : p_data v2 <> 0) by (destruct HC2 as (_ & _ & _ & _ & X & _); exact X).
        rewrite pm_copy_live_app in LV7.
        lazymatch goal with AGx : agree_on (fun a => aclient (rt_live RT S6) _ _ a /\ _) ?ma ?mb |- cps _ (ASTA RT _ _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
          assert (KL12 : keeps_live (rt_live RT S6) ma mb) by (eapply keeps_live_of_agree; [exact AGx| intros e He; exact He| intros; exact I]);
          pose proof (pix_obj_keep _ ma mb pix v cv (keeps_live_sub _ _ ma mb KL12 ltac:(intros e He; rewrite LV6; exact He)) POBJ11) as POBJ12;
          clear KL12 POBJ11 end.
        fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; rewrite LV6; exact (SUB01 e He)| solve [frames_sub_tac]| lia]| exact I]).
        lazymatch goal with A : ART RT S7 ?mm |- cps _ (ASTA RT S7 _ _) _ =>
          assert (FRS7 : rt_frames RT S7 = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity);
          assert (LVP7 : forall p n, In (p, n) (rt_live RT S7) -> 0 < n)
            by (intros p n Hin; rewrite LV7 in Hin; apply in_app_or in Hin; destruct Hin as [Hin|Hin]; [exact (pm_copy_new_pos _ _ _ _ _ POBJC2 VD2 p n Hin)| exact (LVP6 p n Hin)]);
          assert (LEN7 : Z.of_nat (length (rt_live RT S7)) <= Z.of_nat (length (rt_live RT Σ)) + 8)
            by (rewrite LV7, length_app, LV6; pose proof (pm_copy_new_len p2 v2 cv2);
                repeat match goal with H : rt_live RT _ = rt_live RT _ |- _ => rewrite H in * end; lia)
        end.
        hide POBJ12. hide POBJC2.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
        (* [comment removed for export] *)
        Time walk_to AF MST [(usp - 96, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_stack_malloc 1%nat; e_pixDeserialize; e_pixDestroy; e_boxCreate; e_pixCopy; e_pixSetSelectCmap; e_boxDestroy; e_pixSetSelectMaskedCmap; 0x8d7a8].
        unfold hid in POBJ12, POBJC2.
        lazymatch goal with A : ART RT ?S ?m0, MUx : munch _ ?m0 ?m1 |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
          assert (KL13 : keeps_live (rt_live RT S) m0 m1)
            by (apply (keeps_live_walk1 RT AF S m0 m1 fr usp (usp + -96) A ltac:(rewrite FRS7; left; reflexivity)
                         ltac:(repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; unfold STACK_WIN; lia) MUx));
          pose proof (pix_obj_keep _ m0 m1 pix v cv (keeps_live_sub (rt_live RT S) _ m0 m1 KL13 ltac:(intros e He; rewrite LV7; apply in_or_app; right; rewrite LV6; exact He)) POBJ12) as POBJ13;
          pose proof (pix_obj_keep _ m0 m1 p2 v2 cv2 KL13 POBJC2) as POBJC3; clear KL13 end.
        clear POBJ12 POBJC2.
        at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                            repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
        pose proof MSK as MK. unfold pixSetSelectMaskedCmap_cps in MK.
        eapply cps_seq.
        { eapply MK with (lo := lo) (pix := p2) (v := v2) (cv := cv2); rt_side idtac.
          all: lazymatch goal with
               | |- pix_obj _ _ _ _ _ => exact POBJC3
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- lres _ _ _ _ _ =>
                   unfold lres, RASTER_COST, FRAMES_MAX, LIVE_MAX in *; rewrite FRS7, FR0; cbn [length];
                   split; [lia| split; [lia| split; [repeat match goal with H : rt_credit RT _ = _ |- _ => rewrite H in * end; lia| exact LVP7]]]
               | |- ?g => idtac "LEFT-MSK:" g
               end. }
        Time after_call RT AF.
        lazymatch goal with H : rt_live RT ?S = rt_live RT S7 |- _ => rename S into S8; rename H into LV8 end.
        lazymatch goal with |- cps _ (ASTA RT S8 _ (eq (MS _ _ _ _ _ ?mm _))) _ => rename mm into m10 end.
        lazymatch goal with AGx : agree_on (fun a => aclient (rt_live RT S8) _ _ a /\ _) ?ma ?mb |- cps _ (ASTA RT _ _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
          assert (KL14 : keeps_live (rt_live RT S8) ma mb) by (eapply keeps_live_of_agree; [exact AGx| intros e He; exact He| intros; exact I]);
          pose proof (pix_obj_keep _ ma mb pix v cv (keeps_live_sub _ _ ma mb KL14 ltac:(intros e He; rewrite LV8, LV7; apply in_or_app; right; rewrite LV6; exact He)) POBJ13) as POBJ14;
          pose proof (pix_obj_keep _ ma mb p2 v2 cv2 (keeps_live_sub _ _ ma mb KL14 ltac:(intros e He; rewrite LV8; exact He)) POBJC3) as POBJC4;
          clear KL14 POBJ13 POBJC3 end.
        fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; rewrite LV8, LV7; apply in_or_app; right; rewrite LV6; exact (SUB01 e He)| solve [frames_sub_tac]| lia]| exact I]).
        lazymatch goal with A : ART RT S8 ?mm |- cps _ (ASTA RT S8 _ _) _ =>
          assert (FRS8 : rt_frames RT S8 = (fr, 1%nat) :: rt_frames RT Σ)
            by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity);
          assert (LVP8 : forall p n, In (p, n) (rt_live RT S8) -> 0 < n) by (rewrite LV8; exact LVP7) end.
        lazymatch goal with H : rw_cells asegs _ (fr + 96) [C8 (Z_to_bv 64 p2)] |- _ => rename H into PPC2 end.
        hide POBJ14. hide POBJC4.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
        (* [comment removed for export] *)
        Time walk_to AF MST [(usp - 96, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_stack_malloc 1%nat; e_pixDeserialize; e_pixDestroy; e_boxCreate; e_pixCopy; e_pixSetSelectCmap; e_boxDestroy; e_pixSetSelectMaskedCmap; 0x8d7a8].
        unfold hid in POBJ14, POBJC4.
        lazymatch goal with A : ART RT ?S ?m0, MUx : munch _ ?m0 ?m1 |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
          assert (KL15 : keeps_live (rt_live RT S) m0 m1)
            by (apply (keeps_live_walk1 RT AF S m0 m1 fr usp (usp + -96) A ltac:(rewrite FRS8; left; reflexivity)
                         ltac:(repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; unfold STACK_WIN; lia) MUx));
          pose proof (pix_obj_keep _ m0 m1 pix v cv (keeps_live_sub (rt_live RT S) _ m0 m1 KL15 ltac:(intros e He; rewrite LV8, LV7; apply in_or_app; right; rewrite LV6; exact He)) POBJ14) as POBJ15;
          pose proof (pix_obj_keep _ m0 m1 p2 v2 cv2 (keeps_live_sub (rt_live RT S) _ m0 m1 KL15 ltac:(intros e He; rewrite LV8; exact He)) POBJC4) as POBJC5; clear KL15 end.
        clear POBJ14 POBJC4.
        pose proof FSH as SHC. split_at SHC 12%nat SHC12. split_at SHC12 1%nat SHC13. clear SHC SHC13.
        pose proof FR as FRrec. split_before FRrec (C8 s0) FRrec15. clear FRrec.
        at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                            repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
        eapply cps_seq.
        { eapply DY with (lo := lo) (pp := fr + 96) (pix := p2) (v := v2) (cv := cv2) (ras := [RA_TOP]); rt_side idtac.
          all: lazymatch goal with
               | |- optrL _ _ _ _ _ _ =>
                   unfold optrL, parked in *; split;
                   [ right; exists fr, 1%nat; rewrite FRS8; change (fs_size 1) with 128;
                     split; [left; reflexivity|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
                     split; [lia|]; split; [lia|];
                     replace (shad (fr + 96)) with (fr / 8 + 2147450892) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
                     destruct SHC12 as [[_ B] _]; exact B
                   | unfold SEGTOP_A; repeat split; first [lia | clear - FR64; Z.div_mod_to_equations; lia] ]
               | |- rw_cells _ _ _ [C8 _] => exact PPC2
               | |- pix_obj ?lv _ _ _ _ => exact (pix_obj_mono _ lv _ _ _ _ ltac:(intros e He; rewrite LV8; exact He) POBJC5)
               | |- uctx _ _ _ _ =>
                   unfold uctx; rewrite !unsigned_lit by lia; unfold parked in S0INV;
                   apply chain_ok_push with (fp1 := bv_unsigned s0);
                     [ lia | clear - SPA; Z.div_mod_to_equations; lia | unfold USTACK_TOP; lia | unfold RA_TOP; lia | apply bv_unsigned_in_range
                     | rewrite Z_to_bv_bv_unsigned; rewrite <- RATOP; rewrite Z_to_bv_bv_unsigned;
                       lazymatch type of FRrec15 with rw_cells _ _ ?a _ => replace (usp + -16) with a by lia end; exact FRrec15
                     | cbn [chain_ok]; unfold link_invalid; lia ]
               | |- Forall _ _ => pose proof tr_destroy as TD; unfold PM_FUZZ_DESTROY_RAS in TD; exact (Forall_inv (Forall_inv_tail TD))
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- lres _ _ _ _ _ =>
                   unfold lres, RASTER_COST, FRAMES_MAX, LIVE_MAX in *; rewrite FRS8, FR0; cbn [length];
                   split; [lia| split; [rewrite LV8; lia|
                   split; [repeat match goal with H : rt_credit RT _ = _ |- _ => rewrite H in * end; lia| exact LVP8]]]
               | |- ?g => idtac "LEFT-DY2:" g
               end. }
        clear SHC12.
        assert (ANZ2 : p_cmap v2 <> 0 -> c_arr cv2 <> 0)
          by (intros NZ; destruct POBJC5 as (_ & _ & _ & _ & [CZ|((_ & _ & (_ & A0 & _) & _) & _)]); [contradiction| lia]).
        lazymatch goal with A : ART RT S8 ?mm |- _ =>
          assert (ND8 : List.NoDup (map fst (pm_copy_live p2 v2 cv2 (rt_live RT S6))))
            by (pose proof (live_nodup RT AF S8 mm A LVP8) as ND; rewrite LV8, LV7 in ND; rewrite pm_copy_live_app; exact ND) end.
        Time after_call RT AF.
        lazymatch goal with H : rt_live RT ?S = live_destroy p2 v2 cv2 (rt_live RT S8) |- _ => rename S into S9; rename H into LV9r end.
        lazymatch goal with |- cps _ (ASTA RT S9 _ (eq (MS _ _ _ _ _ ?mm _))) _ => rename mm into m11 end.
        assert (LV9 : rt_live RT S9 = rt_live RT S1)
          by (rewrite LV9r, LV8, LV7, <- pm_copy_live_app, (pm_copy_roundtrip p2 v2 cv2 cv2 _ ND8 eq_refl VD2 ANZ2); exact LV6).
        lazymatch goal with AGx : agree_on (fun a => aclient (rt_live RT S9) _ _ a /\ outside [(fr + 96, fr + 96 + 8)] a) ?ma ?mb, A9 : ART RT S9 ?mb |- _ =>
          assert (KL16 : keeps_live (rt_live RT S9) ma mb)
            by (eapply keeps_live_of_agree; [exact AGx| intros e He; exact He|];
                intros qq kk xx Hq Hx; cbn [outside]; split; [| exact I];
                exact (chunk_outside_frame RT AF S9 mb fr 1%nat qq kk (fr + 96) (fr + 96 + 8) xx A9
                         ltac:(repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; left; reflexivity)
                         ltac:(lia) ltac:(change (fs_size 1) with 128; lia) Hq Hx));
          pose proof (pix_obj_keep _ ma mb pix v cv (keeps_live_sub _ _ ma mb KL16 ltac:(intros e He; rewrite LV9; exact He)) POBJ15) as POBJ16;
          clear KL16 end.
        clear POBJ15 POBJC5.
        fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; rewrite LV9; exact (SUB01 e He)| solve [frames_sub_tac]| lia]|
                                        cbn [outside]; destruct (NFA _ Hx) as [N1 N2]; split; [lia| exact I]]).
        lazymatch goal with A : ART RT S9 ?mm |- cps _ (ASTA RT S9 _ _) _ =>
          assert (FRS9 : rt_frames RT S9 = (fr, 1%nat) :: rt_frames RT Σ)
            by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity);
          assert (LVP9 : forall p n, In (p, n) (rt_live RT S9) -> 0 < n) by (rewrite LV9; exact LVP1) end.
        clear ND8 ANZ2 LV9r.
        hide POBJ16.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
        (* [comment removed for export] *)
        Time walk_to AF MST [(usp - 96, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_stack_malloc 1%nat; e_pixDeserialize; e_pixDestroy; e_boxCreate; e_pixCopy; e_pixSetSelectCmap; e_boxDestroy; e_pixSetSelectMaskedCmap; 0x8d7a8].
        unfold hid in POBJ16.
        lazymatch goal with A : ART RT ?S ?m0, MUx : munch _ ?m0 ?m1 |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
          assert (KL17 : keeps_live (rt_live RT S) m0 m1)
            by (apply (keeps_live_walk1 RT AF S m0 m1 fr usp (usp + -96) A ltac:(rewrite FRS9; left; reflexivity)
                         ltac:(repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; unfold STACK_WIN; lia) MUx));
          pose proof (pix_obj_keep _ m0 m1 pix v cv (keeps_live_sub (rt_live RT S) _ m0 m1 KL17 ltac:(intros e He; rewrite LV9; exact He)) POBJ16) as POBJ17;
          clear KL17 end.
        clear POBJ16.
        split_at FRM 4%nat FRMp. split_at FRMp 1%nat FRMq.
        pose proof FSH as SHC. split_at SHC 4%nat SHC4. split_at SHC4 1%nat SHC5. clear SHC SHC5.
        pose proof FR as FRrec. split_before FRrec (C8 s0) FRrec17. clear FRrec.
        at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                            repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
        eapply cps_seq.
        { eapply DY with (lo := lo) (pp := fr + 32) (pix := pix) (v := v) (cv := cv) (ras := [RA_TOP]); rt_side idtac.
          all: lazymatch goal with
               | |- optrL _ _ _ _ _ _ =>
                   unfold optrL, parked in *; split;
                   [ right; exists fr, 1%nat; rewrite FRS9; change (fs_size 1) with 128;
                     split; [left; reflexivity|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
                     split; [lia|]; split; [lia|];
                     replace (shad (fr + 32)) with (fr / 8 + 2147450884) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
                     destruct SHC4 as [[_ B] _]; exact B
                   | unfold SEGTOP_A; repeat split; first [lia | clear - FR64; Z.div_mod_to_equations; lia] ]
               | |- rw_cells _ _ _ [C8 _] => exact FRMp
               | |- pix_obj ?lv _ _ _ _ => exact (pix_obj_mono _ lv _ _ _ _ ltac:(intros e He; rewrite LV9; exact He) POBJ17)
               | |- uctx _ _ _ _ =>
                   unfold uctx; rewrite !unsigned_lit by lia; unfold parked in S0INV;
                   apply chain_ok_push with (fp1 := bv_unsigned s0);
                     [ lia | clear - SPA; Z.div_mod_to_equations; lia | unfold USTACK_TOP; lia | unfold RA_TOP; lia | apply bv_unsigned_in_range
                     | rewrite Z_to_bv_bv_unsigned; rewrite <- RATOP; rewrite Z_to_bv_bv_unsigned;
                       lazymatch type of FRrec17 with rw_cells _ _ ?a _ => replace (usp + -16) with a by lia end; exact FRrec17
                     | cbn [chain_ok]; unfold link_invalid; lia ]
               | |- Forall _ _ => pose proof tr_destroy as TD; unfold PM_FUZZ_DESTROY_RAS in TD; exact (Forall_inv (Forall_inv_tail (Forall_inv_tail TD)))
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- lres _ _ _ _ _ =>
                   unfold lres, RASTER_COST, FRAMES_MAX, LIVE_MAX in *; rewrite FRS9, FR0; cbn [length];
                   split; [lia| split; [rewrite LV9; repeat match goal with H : rt_live RT _ = rt_live RT _ |- _ => rewrite H in * end; lia|
                   split; [repeat match goal with H : rt_credit RT _ = _ |- _ => rewrite H in * end; lia| exact LVP9]]]
               | |- ?g => idtac "LEFT-DY3:" g
               end. }
        clear SHC4.
        Time after_call RT AF.
        lazymatch goal with H : rt_live RT ?S = live_destroy pix v cv (rt_live RT S9) |- _ => rename S into S10; rename H into LV10r end.
        lazymatch goal with |- cps _ (ASTA RT S10 _ (eq (MS _ _ _ _ _ ?mm _))) _ => rename mm into m12 end.
        (* [comment removed for export] *)
        assert (LV10 : rt_live RT S10 = rt_live RT Σ)
          by (rewrite LV10r, LV9, LVE; repeat match goal with H : rt_live RT _ = rt_live RT Σ |- _ => rewrite H end; reflexivity).
        clear POBJ17.
        fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; rewrite LV10; exact He| solve [frames_sub_tac]| lia]|
                                        cbn [outside]; destruct (NFA _ Hx) as [N1 N2]; split; [lia| exact I]]).
        clear LV10r PIN IN.
        (* [comment removed for export] *)
        repeat match goal with H : rw_cells asegs _ (usp + -16) _ |- _ => clear H end.
        repeat match goal with H : rw_cells asegs _ (fr + _) _ |- _ => clear H end.
        repeat match goal with H : ART RT _ ?mm |- cps _ (ASTA RT _ _ (eq (MS _ _ _ _ _ ?mc _))) _ => lazymatch mm with mc => fail | m => fail | _ => clear H end end.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
        (* [comment removed for export] *)
        Time walk_to AF MST [(usp - 96, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_stack_malloc 1%nat; e_pixDeserialize; e_pixDestroy; e_boxCreate; e_pixCopy; e_pixSetSelectCmap; e_boxDestroy; e_pixSetSelectMaskedCmap; 0x8d7a8].
        Time frame_release_g RT AF GP MST Σ fr 1%nat 128 PF AGF PFS usp lo 0x8d7b0
          ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
          ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                            repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia])
          ltac:(fun Hx => exact (proj1 Hx)) ltac:(fun fl FLN => idtac).
        refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
        Time walk_to AF MST [(usp - 96, usp)] (@nil Z).
        try (lazymatch goal with ST' : stk asegs _ lo (usp + -96) |- _ => release_frame FR ST' usp end).   (* [comment removed for export] *)
        cps_stop.
        apply cps_finish; intros c Hc; subst QF; cbv beta.
        lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S end.
        split; [| unfold RASTER_COST in *; alg_tac].
        eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-; eexists.
        split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
        split; [split; [assumption| split; assumption]|].
        split; [intros a Ha Ho; exact (AGF a (conj Ha Ho))|].
        lazymatch goal with LHx : LIBH ?mm |- LIB ?mm => destruct LHx as (LH0 & LHH); split; [exact LH0| eexists; exact LHH] end.
  - (* [comment removed for export] *)
    carve_frame 112%nat ST.
    walk_to AF MST [(usp - 112, usp)] [e_stack_malloc 1%nat; e_pixDeserialize; e_pixDestroy; e_boxCreate; e_pixCopy; e_pixSetSelectCmap; e_boxDestroy; e_pixSetSelectMaskedCmap; 0x8d7a8].
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
    eapply cps_seq.
    { pose proof (gp_stack_malloc_1 RT GP) as SM0; unfold stack_malloc_contract' in SM0; eapply SM0 with (lo := lo); rt_side idtac. }
    after_call RT AF.
    fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]).
    fframe_open RT AF PF (rt_live RT Σ) usp 1%nat 128 ltac:(fun Ha => exact (proj1 Ha)).
    refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
    destruct (Z_lt_ge_dec (Z.of_nat (length bs)) 3) as [SZ|SZ].
    + (* [comment removed for export] *)
      walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_stack_malloc 1%nat; e_pixDeserialize; e_pixDestroy; e_boxCreate; e_pixCopy; e_pixSetSelectCmap; e_boxDestroy; e_pixSetSelectMaskedCmap; 0x8d7a8].
      frame_release_raw RT AF GP MST Σ fr 1%nat 128 PF AGF PFS usp lo 0x8d7b0
        ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
        ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                          repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia])
        ltac:(fun Hx => exact (proj1 Hx)) LSEV LALLOC LDEALLOC LHAND.
      refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
      walk_to AF MST [(usp - 112, usp)] (@nil Z).
      try (lazymatch goal with ST' : stk asegs _ lo (usp + -112) |- _ => release_frame FR ST' usp end).   (* [comment removed for export] *)
      cps_stop.
      apply cps_finish; intros c Hc; subst QF; cbv beta.
      lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S end.
      split; [| alg_tac].
      eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-; eexists.
      split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
      split; [split; [assumption| split; assumption]|].
      split; [intros a Ha Ho; exact (AGF a (conj Ha Ho))|].
      unfold LIB, LIB0, g_LeptMsgSeverity, g_pix_alloc, g_pix_dealloc, g_stderr_handler.
      split; [split; [assumption| split; assumption]| exists h0; assumption].
    + (* [comment removed for export] *)
      walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16); (858208, 858216)]
                   [e_stack_malloc 1%nat; e_pixDeserialize; e_pixDestroy; e_boxCreate; e_pixCopy; e_pixSetSelectCmap; e_boxDestroy; e_pixSetSelectMaskedCmap; 0x8d7a8].
      destruct OWN as [(p0 & n0 & OIN & OLO & OHI & DAL)| ->]; [| cbn [length] in SZ; lia].
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (LH : LIBH mm)
        by (unfold LIBH, LIB0, g_LeptMsgSeverity, g_pix_alloc, g_pix_dealloc, g_stderr_handler, e_devnull; split; [split; [|split]|]; assumption) end.
      clear LSEV LALLOC LDEALLOC LHAND.
      pose proof FR as FRrec. split_before FRrec (C8 s0) FRrec2. clear FRrec.
      at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| split; [intros zz Hzz; static_tac | exact I]]]])
                    ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; destruct Hx as [_ HxO];
                          unfold Lept_iface.LIB_FP, g_stderr_handler in HxO; cbn [outside] in HxO; unfold shad, SHB in *;
                          repeat split; try exact I; first [lia | tauto | Z.div_mod_to_equations; lia]).
      pose proof DESER as DS. unfold pixDeserialize_cps in DS.
      eapply cps_seq.
      { eapply DS with (lo := lo) (dp := d) (n := Z.of_nat (length bs)) (ras := [RA_TOP]); rt_side idtac.
        - right. split; [exact DAL|]. exists p0, n0. repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end. split; [exact OIN | lia].
        - unfold uctx. (rewrite !unsigned_lit by lia). unfold parked in S0INV.
          (apply chain_ok_push with (fp1 := bv_unsigned s0)).
          + lia.
          + (clear - SPA; Z.div_mod_to_equations; lia).
          + (unfold USTACK_TOP; lia).
          + (unfold RA_TOP; lia).
          + (apply bv_unsigned_in_range).
          + (rewrite Z_to_bv_bv_unsigned; rewrite <- RATOP; rewrite Z_to_bv_bv_unsigned).
            (lazymatch type of FRrec2 with rw_cells _ _ ?a _ => replace (usp + -16) with a by lia end). (exact FRrec2).
          + (cbn [chain_ok]; unfold link_invalid; lia).
        - (exact tr_deser).
        - lenv_tac.
        - unfold RASTER_COST. lres_tac. }
      after_call RT AF.
      fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]| exact I]).
      lazymatch goal with H : ?p = 0 \/ _ |- _ => rename H into POBJ; set (pix := p) in * end.
      lazymatch goal with H : pix = 0 -> rt_live RT _ = _ |- _ => rename H into LVZ end.
      lazymatch goal with H : pix <> 0 -> live_destroy _ _ _ _ = _ |- _ => rename H into LVD end.
      match goal with H : forall p n, In (p, n) (rt_live RT ?S) -> 0 < n |- _ => lazymatch S with Σ => fail | _ => rename H into LVP1 end end.
      match goal with H : Z.of_nat (length (rt_live RT _)) <= Z.of_nat (length (rt_live RT _)) + 4 |- _ => rename H into LEN1 end.
      match goal with H : rt_credit RT _ - _ <= rt_credit RT _ |- _ => rename H into CR1 end.
      destruct (Z.eq_dec pix 0) as [PZ|PNZ].
      * (* [comment removed for export] *)
        clear POBJ LVD. pose proof (LVZ PZ) as LVE. clear LVZ. rewrite PZ in *.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
        walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_stack_malloc 1%nat; e_pixDeserialize; e_pixDestroy; e_boxCreate; e_pixCopy; e_pixSetSelectCmap; e_boxDestroy; e_pixSetSelectMaskedCmap; 0x8d7a8].
        frame_release_g RT AF GP MST Σ fr 1%nat 128 PF AGF PFS usp lo 0x8d7b0
          ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
          ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                            repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia])
          ltac:(fun Hx => exact (proj1 Hx)) ltac:(fun fl FLN => idtac).
        refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
        walk_to AF MST [(usp - 112, usp)] (@nil Z).
        try (lazymatch goal with ST' : stk asegs _ lo (usp + -112) |- _ => release_frame FR ST' usp end).   (* [comment removed for export] *)
        cps_stop.
        apply cps_finish; intros c Hc; subst QF; cbv beta.
        lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S end.
        split; [| unfold RASTER_COST in *; alg_tac].
        eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-; eexists.
        split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
        split; [split; [assumption| split; assumption]|].
        split; [intros a Ha Ho; exact (AGF a (conj Ha Ho))|].
        lazymatch goal with LHx : LIBH ?mm |- LIB ?mm => destruct LHx as (LH0 & LHH); split; [exact LH0| eexists; exact LHH] end.
      * (* [comment removed for export] *)
        destruct POBJ as [PZ|(POBJ & VDATA)]; [contradiction|]. clear LVZ. pose proof (LVD PNZ) as LVE. clear LVD.
        lazymatch type of POBJ with pix_obj _ _ _ ?vv ?cc => set (v := vv) in *; set (cv := cc) in * end.
        pose proof POBJ as (PXC & (PIN & PX0 & PX16 & _) & _). clear PXC.
        chunk_facts RT AF GP pix 64.
        lazymatch type of PIN with In _ (rt_live RT ?S1) =>
          assert (SUB01 : forall e, In e (rt_live RT Σ) -> In e (rt_live RT S1))
            by (intros e He; apply (live_destroy_sub pix v cv); rewrite LVE; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact He) end.
        lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ =>
          assert (FRSh : rt_frames RT S = (fr, 1%nat) :: rt_frames RT Σ)
            by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity) end.
        hide POBJ.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
        (* [comment removed for export] *)
        Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_stack_malloc 1%nat; e_pixDeserialize; e_pixDestroy; e_boxCreate; e_pixCopy; e_pixSetSelectCmap; e_boxDestroy; e_pixSetSelectMaskedCmap; 0x8d7a8].
        unfold hid in POBJ.
        lazymatch goal with A : ART RT ?S ?m0, MUx : munch _ ?m0 ?m1 |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
          assert (KL1 : keeps_live (rt_live RT S) m0 m1)
            by (apply (keeps_live_walk1 RT AF S m0 m1 fr usp (usp + -112) A ltac:(rewrite FRSh; left; reflexivity)
                         ltac:(repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; unfold STACK_WIN; lia) MUx));
          pose proof (pix_obj_keep _ m0 m1 pix v cv KL1 POBJ) as POBJ1; clear KL1 end.
        clear POBJ.
        at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                            repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
        pose proof BOXC as BC. unfold boxCreate_cps in BC.
        eapply cps_seq.
        { eapply BC with (lo := lo) (x := 278) (y := 35) (w := 122) (h := 50); rt_side idtac.
          all: lazymatch goal with
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- lres _ _ _ _ _ =>
                   unfold lres, RASTER_COST, FRAMES_MAX, LIVE_MAX in *; rewrite FRSh, FR0; cbn [length];
                   repeat match goal with H : rt_live RT _ = rt_live RT _ |- _ => rewrite H in * end;
                   repeat match goal with H : rt_credit RT _ = _ |- _ => rewrite H in * end;
                   split; [lia| split; [lia| split; [lia| exact LVP1]]]
               | |- ?g => idtac "LEFT-BOXC:" g
               end. }
        after_call RT AF.
        lazymatch goal with H : box_obj _ _ ?bb 278 35 122 50 |- _ => rename H into BOBJ; set (b := bb) in * end.
        lazymatch goal with H : rt_live RT _ = (b, 20) :: _ |- _ => rename H into LV2 end.
        lazymatch goal with AGx : agree_on _ ?ma ?mb |- cps _ (ASTA RT _ _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
          assert (KL2 : keeps_live (rt_live RT _) ma mb) by (eapply keeps_live_of_agree; [exact AGx| intros e He; exact He| intros; exact I]);
          pose proof (pix_obj_keep _ ma mb pix v cv KL2 POBJ1) as POBJ2; clear KL2 POBJ1 end.
        fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [exact SUB01| solve [frames_sub_tac]| lia]| exact I]).
        lazymatch goal with A : ART RT ?S2 ?mm |- cps _ (ASTA RT ?S2 _ _) _ =>
          assert (FRS2 : rt_frames RT S2 = (fr, 1%nat) :: rt_frames RT Σ)
            by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity);
          assert (LVP2 : forall p n, In (p, n) (rt_live RT S2) -> 0 < n)
            by (intros p n Hin; rewrite LV2 in Hin; destruct Hin as [E|Hin]; [injection E as <- <-; lia| exact (LVP1 p n Hin)]) end.
        hide POBJ2. hide BOBJ.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
        (* [comment removed for export] *)
        Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_stack_malloc 1%nat; e_pixDeserialize; e_pixDestroy; e_boxCreate; e_pixCopy; e_pixSetSelectCmap; e_boxDestroy; e_pixSetSelectMaskedCmap; 0x8d7a8].
        unfold hid in POBJ2, BOBJ.
        lazymatch goal with A : ART RT ?S ?m0, MUx : munch _ ?m0 ?m1 |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
          assert (KL3 : keeps_live (rt_live RT S) m0 m1)
            by (apply (keeps_live_walk1 RT AF S m0 m1 fr usp (usp + -112) A ltac:(rewrite FRS2; left; reflexivity)
                         ltac:(repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; unfold STACK_WIN; lia) MUx));
          pose proof (pix_obj_keep _ m0 m1 pix v cv (keeps_live_sub (rt_live RT S) _ m0 m1 KL3 ltac:(intros e He; rewrite LV2; right; exact He)) POBJ2) as POBJ3;
          pose proof (box_obj_keep _ m0 m1 b 278 35 122 50 BOBJ (keeps_live_sub (rt_live RT S) [(b, 20)] m0 m1 KL3 ltac:(intros e [<-|[]]; rewrite LV2; left; reflexivity))) as BOBJ3;
          clear KL3 end.
        clear POBJ2 BOBJ.
        at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                            repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
        pose proof COPY as CP. unfold pixCopy_nn_cps in CP.
        eapply cps_seq.
        { eapply CP with (lo := lo) (pixs := pix) (v := v) (cv := cv); rt_side idtac.
          all: lazymatch goal with
               | |- pix_obj ?lv _ _ _ _ => apply (pix_obj_mono _ lv _ _ _ _ ltac:(intros e He; rewrite LV2; right; exact He) POBJ3)
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- lres _ _ _ _ _ =>
                   unfold lres, RASTER_COST, FRAMES_MAX, LIVE_MAX in *; rewrite FRS2, FR0, LV2; cbn [length];
                   repeat match goal with H : rt_live RT _ = rt_live RT _ |- _ => rewrite H in * end;
                   repeat match goal with H : rt_credit RT _ = _ |- _ => rewrite H in * end;
                   split; [lia| split; [lia| split; [lia| rewrite <- LV2; exact LVP2]]]
               | |- ?g => idtac "LEFT-COPY1:" g
               end. }
        after_call RT AF.
        (* [comment removed for export] *)
        lazymatch goal with HC : pm_hdr_copy _ ?vv _ ?cc |- _ =>
          lazymatch goal with H : pix_obj _ _ ?p vv cc |- _ => rename H into POBJC; rename HC into HC1; set (p1 := p) in *; set (v1 := vv) in *; set (cv1 := cc) in * end end.
        lazymatch goal with H : p1 <> 0 |- _ => rename H into P1NZ end.
        lazymatch goal with H : rt_live RT _ = pm_copy_live p1 v1 cv1 _ |- _ => rename H into LV3 end.
        assert (VD1 : p_data v1 <> 0) by (destruct HC1 as (_ & _ & _ & _ & X & _); exact X).
        rewrite pm_copy_live_app in LV3.
        lazymatch goal with AGx : agree_on (fun a => aclient ?lv _ _ a /\ _) ?ma ?mb |- cps _ (ASTA RT _ _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
          assert (KL4 : keeps_live lv ma mb) by (eapply keeps_live_of_agree; [exact AGx| intros e He; exact He| intros; exact I]);
          pose proof (pix_obj_keep _ ma mb pix v cv (keeps_live_sub lv _ ma mb KL4 ltac:(intros e He; rewrite LV2; right; exact He)) POBJ3) as POBJ4;
          pose proof (box_obj_keep _ ma mb b 278 35 122 50 BOBJ3 (keeps_live_sub lv [(b, 20)] ma mb KL4 ltac:(intros e [<-|[]]; rewrite LV2; left; reflexivity))) as BOBJ4;
          clear KL4 POBJ3 BOBJ3 end.
        fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; rewrite LV2; right; exact (SUB01 e He)| solve [frames_sub_tac]| lia]| exact I]).
        lazymatch goal with A : ART RT ?S3 ?mm |- cps _ (ASTA RT ?S3 _ _) _ =>
          assert (FRS3 : rt_frames RT S3 = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity);
          assert (LVP3 : forall p n, In (p, n) (rt_live RT S3) -> 0 < n)
            by (intros p n Hin; rewrite LV3 in Hin; apply in_app_or in Hin; destruct Hin as [Hin|Hin]; [exact (pm_copy_new_pos _ _ _ _ _ POBJC VD1 p n Hin)| exact (LVP2 p n Hin)]);
          assert (SUB23 : forall e, In e (rt_live RT _) -> In e (rt_live RT S3)) by (intros e He; rewrite LV3; apply in_or_app; right; exact He);
          assert (LEN3 : Z.of_nat (length (rt_live RT S3)) <= Z.of_nat (length (rt_live RT Σ)) + 9)
            by (rewrite LV3, length_app, LV2; cbn [length]; pose proof (pm_copy_new_len p1 v1 cv1);
                repeat match goal with H : rt_live RT _ = rt_live RT _ |- _ => rewrite H in * end; lia);
          assert (NEB : b <> p1)
            by (pose proof (live_apart_app RT AF S3 mm _ _ p1 64 b 20 A LV3 ltac:(unfold pm_copy_new; apply in_or_app; right; right; left; reflexivity) ltac:(rewrite LV2; left; reflexivity)); lia)
        end.
        park LV3. hide POBJ4. hide BOBJ4. hide POBJC. hide NEB.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
        (* [comment removed for export] *)
        Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_stack_malloc 1%nat; e_pixDeserialize; e_pixDestroy; e_boxCreate; e_pixCopy; e_pixSetSelectCmap; e_boxDestroy; e_pixSetSelectMaskedCmap; 0x8d7a8].
        unfold hid in POBJ4, BOBJ4, POBJC, NEB.
        lazymatch goal with A : ART RT ?S ?m0, MUx : munch _ ?m0 ?m1 |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
          assert (KL5 : keeps_live (rt_live RT S) m0 m1)
            by (apply (keeps_live_walk1 RT AF S m0 m1 fr usp (usp + -112) A ltac:(rewrite FRS3; left; reflexivity)
                         ltac:(repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; unfold STACK_WIN; lia) MUx));
          pose proof (pix_obj_keep _ m0 m1 pix v cv (keeps_live_sub (rt_live RT S) _ m0 m1 KL5 ltac:(intros e He; apply SUB23; rewrite LV2; right; exact He)) POBJ4) as POBJ5;
          pose proof (box_obj_keep _ m0 m1 b 278 35 122 50 BOBJ4 (keeps_live_sub (rt_live RT S) [(b, 20)] m0 m1 KL5 ltac:(intros e [<-|[]]; apply SUB23; rewrite LV2; left; reflexivity))) as BOBJ5;
          pose proof (pix_obj_keep _ m0 m1 p1 v1 cv1 KL5 POBJC) as POBJC5; clear KL5 end.
        clear POBJ4 BOBJ4 POBJC.
        at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                            repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
        pose proof SEL as SL. unfold pixSetSelectCmap_cps in SL.
        eapply cps_seq.
        { eapply SL with (lo := lo) (pix := p1) (b := b) (v := v1) (cv := cv1); rt_side idtac.
          all: lazymatch goal with
               | |- box_obj ?lv _ _ _ _ _ _ => exact (box_obj_mono _ lv _ _ _ _ _ _ SUB23 BOBJ5)
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- lres _ _ _ _ _ =>
                   unfold lres, RASTER_COST, FRAMES_MAX, LIVE_MAX in *; rewrite FRS3, FR0; cbn [length];
                   repeat match goal with H : rt_credit RT _ = _ |- _ => rewrite H in * end;
                   split; [lia| split; [lia| split; [lia| exact LVP3]]]
               | |- ?g => idtac "LEFT-SEL:" g
               end. }
        (* [comment removed for export] *)
        lazymatch type of LVE with live_destroy _ _ _ (rt_live RT ?S) = _ => rename S into S1 end.
        lazymatch type of LV2 with rt_live RT ?S = _ => rename S into S2 end.
        lazymatch type of LV3 with parked (rt_live RT ?S = _) => rename S into S3 end.
        (* [comment removed for export] *)
        cps_open RT. after_call_unfold. fold_zdefs. unfold rt_after, rt_after_f in *. split_hyps.
        unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *.
        repeat match goal with H : context [bv_unsigned (Z_to_bv 64 ?e)] |- _ => rewrite (unsigned_lit e) in H by lia end.
        lazymatch goal with P : rt_pres_fp (rt_live RT ?S4) (rt_frames RT ?S3) ?spc (pm_fp v1 cv1) ?ma ?mb, E4 : rt_live RT ?S4 = rt_live RT ?S3 |- _ =>
          assert (AG : agree_on (aclient (rt_live RT S2) (rt_frames RT S3) spc) ma mb)
            by (intros a Ha; apply P;
                [ apply (aclient_mono _ _ _ _ _ _ _ Ha); [rewrite E4; exact SUB23| intros e He; exact He| lia]
                | unfold parked in LV3;
                  exact (tail_client_outside RT AF S3 ma (pm_copy_new p1 v1 cv1) (rt_live RT S2) (rt_live RT S2) (rt_frames RT S3) spc _ (pm_fp v1 cv1)
                           ARTc3 LV3 (pm_fp_in_new p1 v1 cv1) (fun e He => He) (fun e He => He)
                           ltac:(repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; unfold STACK_WIN; lia) Ha) ]);
          clear P
        end.
        Time lazymatch goal with AGx : agree_on (aclient (rt_live RT S2) _ _) ?ma ?mb |- _ => rt_transport ma mb AGx ltac:(fun A => acl_dispatch A) end.
        fix_ret_pc.
        lazymatch goal with AGx : agree_on (aclient (rt_live RT S2) _ _) ?ma ?mb |- _ =>
          pose proof (keeps_live_of_agf _ _ _ ma mb AGx) as KL6;
          pose proof (pix_obj_keep _ ma mb pix v cv (keeps_live_sub _ _ ma mb KL6 ltac:(intros e He; rewrite LV2; right; exact He)) POBJ5) as POBJ6;
          pose proof (box_obj_keep _ ma mb b 278 35 122 50 BOBJ5 (keeps_live_sub _ [(b, 20)] ma mb KL6 ltac:(intros e [<-|[]]; rewrite LV2; left; reflexivity))) as BOBJ6;
          clear KL6 POBJ5 BOBJ5 POBJC5 end.
        fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; rewrite LV2; right; exact (SUB01 e He)| solve [frames_sub_tac]| lia]).
        lazymatch goal with H : rt_live RT ?S = rt_live RT S3 |- _ => rename S into S4; rename H into LV4 end.
        lazymatch goal with |- cps _ (ASTA RT S4 _ (eq (MS _ _ _ _ _ ?mm _))) _ => rename mm into m5 end.
        lazymatch goal with H : pix_obj (rt_live RT S4) m5 p1 v1 ?c |- _ => rename H into POBJC6; set (cv1' := c) in * end.
        lazymatch goal with H : c_arr cv1' = c_arr cv1 |- _ => rename H into CA1 end.
        lazymatch goal with H : c_nalloc cv1' = c_nalloc cv1 |- _ => rename H into CN1 end.
        lazymatch goal with H : rt_credit RT S3 - 4 <= rt_credit RT S4 |- _ => rename H into CR4 end.

        lazymatch goal with A : ART RT S4 ?mm |- cps _ (ASTA RT S4 _ _) _ =>
          assert (FRS4 : rt_frames RT S4 = (fr, 1%nat) :: rt_frames RT Σ)
            by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity);
          assert (LVP4 : forall p n, In (p, n) (rt_live RT S4) -> 0 < n) by (rewrite LV4; exact LVP3) end.
        hide POBJ6. hide BOBJ6. hide POBJC6.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
        (* [comment removed for export] *)
        Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_stack_malloc 1%nat; e_pixDeserialize; e_pixDestroy; e_boxCreate; e_pixCopy; e_pixSetSelectCmap; e_boxDestroy; e_pixSetSelectMaskedCmap; 0x8d7a8].
        unfold hid in POBJ6, BOBJ6, POBJC6.
        lazymatch goal with A : ART RT ?S ?m0, MUx : munch _ ?m0 ?m1 |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
          assert (KL7 : keeps_live (rt_live RT S) m0 m1)
            by (apply (keeps_live_walk1 RT AF S m0 m1 fr usp (usp + -112) A ltac:(rewrite FRS4; left; reflexivity)
                         ltac:(repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; unfold STACK_WIN; lia) MUx));
          pose proof (pix_obj_keep _ m0 m1 pix v cv (keeps_live_sub (rt_live RT S) _ m0 m1 KL7 ltac:(intros e He; rewrite LV4; apply SUB23; rewrite LV2; right; exact He)) POBJ6) as POBJ7;
          pose proof (box_obj_keep _ m0 m1 b 278 35 122 50 BOBJ6 (keeps_live_sub (rt_live RT S) [(b, 20)] m0 m1 KL7 ltac:(intros e [<-|[]]; rewrite LV4; apply SUB23; rewrite LV2; left; reflexivity))) as BOBJ7;
          pose proof (pix_obj_keep _ m0 m1 p1 v1 cv1' KL7 POBJC6) as POBJC7; clear KL7 end.
        clear POBJ6 BOBJ6 POBJC6.
        split_at FRM 6%nat FRMb. split_at FRMb 1%nat FRMc.
        pose proof FSH as SHC. split_at SHC 8%nat SHC8. split_at SHC8 1%nat SHC9. clear SHC SHC9.
        at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                            repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
        pose proof BOXD as BD. unfold boxDestroy_cps in BD.
        eapply cps_seq.
        { eapply BD with (lo := lo) (pp := fr + 64) (b := b) (x := 278) (y := 35) (w := 122) (h := 50); rt_side idtac.
          all: lazymatch goal with
               | |- optrF _ _ _ _ _ =>
                   unfold optrF, own_frame, parked in *; split;
                   [ exists fr, 1%nat; rewrite FRS4; change (fs_size 1) with 128;
                     split; [left; reflexivity|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
                     split; [lia|]; split; [lia|];
                     replace (shad (fr + 64)) with (fr / 8 + 2147450888) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
                     destruct SHC8 as [[_ B] _]; exact B
                   | unfold SEGTOP_A; repeat split; first [lia | clear - FR64; Z.div_mod_to_equations; lia] ]
               | |- rw_cells _ _ _ [C8 _] => exact FRMb
               | |- box_obj ?lv _ _ _ _ _ _ => exact (box_obj_mono _ lv _ _ _ _ _ _ ltac:(intros e He; rewrite LV4; exact (SUB23 e He)) BOBJ7)
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- forall p n, In (p, n) _ -> 0 < n => exact LVP4
               | |- ?g => idtac "LEFT-BD:" g
               end. }
        clear SHC8.
        Time after_call RT AF.
        lazymatch goal with H : rt_live RT ?S = live_remove b (rt_live RT S4) |- _ => rename S into S5; rename H into LV5r end.
        lazymatch goal with |- cps _ (ASTA RT S5 _ (eq (MS _ _ _ _ _ ?mm _))) _ => rename mm into m6 end.
        (* [comment removed for export] *)
        lazymatch goal with A : ART RT S4 m5 |- _ =>
          assert (ND4 : List.NoDup (map fst (pm_copy_live p1 v1 cv1 ((b, 20) :: rt_live RT S1))))
            by (pose proof (live_nodup RT AF S4 m5 A LVP4) as ND; rewrite LV4 in ND; unfold parked in LV3; rewrite LV3, LV2 in ND;
                rewrite pm_copy_live_app; exact ND) end.
        assert (LV5 : rt_live RT S5 = pm_copy_new p1 v1 cv1 ++ rt_live RT S1)
          by (rewrite LV5r, LV4; unfold parked in LV3; rewrite LV3, LV2, <- pm_copy_live_app, (pm_copy_live_remove_box b 20 p1 v1 cv1 _ ND4), pm_copy_live_app; reflexivity).
        lazymatch goal with AGx : agree_on (fun a => aclient (rt_live RT S5) _ _ a /\ outside [(fr + 64, fr + 64 + 8)] a) ?ma ?mb, A5 : ART RT S5 ?mb |- _ =>
          assert (KL8 : keeps_live (rt_live RT S5) ma mb)
            by (eapply keeps_live_of_agree; [exact AGx| intros e He; exact He|];
                intros qq kk xx Hq Hx; cbn [outside]; split; [| exact I];
                exact (chunk_outside_frame RT AF S5 mb fr 1%nat qq kk (fr + 64) (fr + 64 + 8) xx A5
                         ltac:(repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; left; reflexivity)
                         ltac:(lia) ltac:(change (fs_size 1) with 128; lia) Hq Hx));
          pose proof (pix_obj_keep _ ma mb pix v cv (keeps_live_sub _ _ ma mb KL8 ltac:(intros e He; rewrite LV5; apply in_or_app; right; exact He)) POBJ7) as POBJ8;
          pose proof (pix_obj_move _ (rt_live RT S5) ma mb p1 v1 cv1' POBJC7
                        ltac:(intros e He; rewrite LV5; apply in_or_app; left; exact (pix_chunks_new p1 v1 cv1 cv1' CA1 CN1 e He))
                        (keeps_live_sub _ [(p1, 64)] ma mb KL8 ltac:(intros e [<-|[]]; rewrite LV5; apply in_or_app; left;
                                                                     apply (pix_chunks_new p1 v1 cv1 cv1' CA1 CN1); unfold pix_chunks; left; reflexivity))
                        (fun NZ => keeps_live_sub _ [(p_cmap v1, 24)] ma mb KL8 ltac:(intros e [<-|[]]; rewrite LV5; apply in_or_app; left;
                                     apply (pix_chunks_new p1 v1 cv1 cv1' CA1 CN1); unfold pix_chunks; right; apply in_or_app; right;
                                     replace (p_cmap v1 =? 0) with false by (symmetry; apply Z.eqb_neq; exact NZ); left; reflexivity))) as POBJC8;
          clear KL8 end.
        clear POBJ7 BOBJ7 POBJC7.
        fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; rewrite LV5; apply in_or_app; right; exact (SUB01 e He)| solve [frames_sub_tac]| lia]|
                                        cbn [outside]; destruct (NFA _ Hx) as [N1 N2]; split; [lia| exact I]]).
        lazymatch goal with A : ART RT S5 ?mm |- cps _ (ASTA RT S5 _ _) _ =>
          assert (FRS5 : rt_frames RT S5 = (fr, 1%nat) :: rt_frames RT Σ)
            by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity);
          assert (LVP5 : forall p n, In (p, n) (rt_live RT S5) -> 0 < n)
            by (intros p n Hin; rewrite LV5r in Hin; exact (LVP4 p n (live_remove_sub _ _ _ Hin))) end.
        hide POBJ8. hide POBJC8.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
        (* [comment removed for export] *)
        Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_stack_malloc 1%nat; e_pixDeserialize; e_pixDestroy; e_boxCreate; e_pixCopy; e_pixSetSelectCmap; e_boxDestroy; e_pixSetSelectMaskedCmap; 0x8d7a8].
        unfold hid in POBJ8, POBJC8.
        lazymatch goal with A : ART RT ?S ?m0, MUx : munch _ ?m0 ?m1 |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
          assert (KL9 : keeps_live (rt_live RT S) m0 m1)
            by (apply (keeps_live_walk1 RT AF S m0 m1 fr usp (usp + -112) A ltac:(rewrite FRS5; left; reflexivity)
                         ltac:(repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; unfold STACK_WIN; lia) MUx));
          pose proof (pix_obj_keep _ m0 m1 pix v cv (keeps_live_sub (rt_live RT S) _ m0 m1 KL9 ltac:(intros e He; rewrite LV5; apply in_or_app; right; exact He)) POBJ8) as POBJ9;
          pose proof (pix_obj_keep _ m0 m1 p1 v1 cv1' KL9 POBJC8) as POBJC9; clear KL9 end.
        clear POBJ8 POBJC8.
        split_at FRMc 1%nat FRMd. split_at FRMd 1%nat FRMe.
        pose proof FSH as SHC. split_at SHC 12%nat SHC12. split_at SHC12 1%nat SHC13. clear SHC SHC13.
        pose proof FR as FRrec. split_before FRrec (C8 s0) FRrec9. clear FRrec.
        at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                            repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
        pose proof DESTROY as DY. unfold pixDestroy_cps in DY.
        eapply cps_seq.
        { eapply DY with (lo := lo) (pp := fr + 96) (pix := p1) (v := v1) (cv := cv1') (ras := [RA_TOP]); rt_side idtac.
          all: lazymatch goal with
               | |- optrL _ _ _ _ _ _ =>
                   unfold optrL, parked in *; split;
                   [ right; exists fr, 1%nat; rewrite FRS5; change (fs_size 1) with 128;
                     split; [left; reflexivity|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
                     split; [lia|]; split; [lia|];
                     replace (shad (fr + 96)) with (fr / 8 + 2147450892) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
                     destruct SHC12 as [[_ B] _]; exact B
                   | unfold SEGTOP_A; repeat split; first [lia | clear - FR64; Z.div_mod_to_equations; lia] ]
               | |- rw_cells _ _ _ [C8 _] => exact FRMd
               | |- pix_obj _ _ _ _ _ => exact POBJC9
               | |- uctx _ _ _ _ =>
                   unfold uctx; rewrite !unsigned_lit by lia; unfold parked in S0INV;
                   apply chain_ok_push with (fp1 := bv_unsigned s0);
                     [ lia | clear - SPA; Z.div_mod_to_equations; lia | unfold USTACK_TOP; lia | unfold RA_TOP; lia | apply bv_unsigned_in_range
                     | rewrite Z_to_bv_bv_unsigned; rewrite <- RATOP; rewrite Z_to_bv_bv_unsigned;
                       lazymatch type of FRrec9 with rw_cells _ _ ?a _ => replace (usp + -16) with a by lia end; exact FRrec9
                     | cbn [chain_ok]; unfold link_invalid; lia ]
               | |- Forall _ _ => pose proof tr_destroy as TD; unfold PM_FUZZ_DESTROY_RAS in TD; exact (Forall_inv TD)
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- lres _ _ _ _ _ =>
                   unfold lres, RASTER_COST, FRAMES_MAX, LIVE_MAX in *; rewrite FRS5, FR0; cbn [length];
                   split; [lia| split; [rewrite LV5, length_app; pose proof (pm_copy_new_len p1 v1 cv1);
                                        repeat match goal with H : rt_live RT _ = rt_live RT _ |- _ => rewrite H in * end; lia|
                   split; [repeat match goal with H : rt_credit RT _ = _ |- _ => rewrite H in * end; lia| exact LVP5]]]
               | |- ?g => idtac "LEFT-DY1:" g
               end. }
        clear SHC12.
        assert (ANZ1 : p_cmap v1 <> 0 -> c_arr cv1 <> 0)
          by (intros NZ; destruct POBJC9 as (_ & _ & _ & _ & [CZ|((_ & _ & (_ & A0 & _) & _) & _)]); [contradiction| rewrite <- CA1; lia]).
        lazymatch goal with A : ART RT S5 ?mm |- _ =>
          assert (ND5 : List.NoDup (map fst (pm_copy_live p1 v1 cv1 (rt_live RT S1))))
            by (pose proof (live_nodup RT AF S5 mm A LVP5) as ND; rewrite LV5 in ND; rewrite pm_copy_live_app; exact ND) end.
        Time after_call RT AF.
        lazymatch goal with H : rt_live RT ?S = live_destroy p1 v1 cv1' (rt_live RT S5) |- _ => rename S into S6; rename H into LV6r end.
        lazymatch goal with |- cps _ (ASTA RT S6 _ (eq (MS _ _ _ _ _ ?mm _))) _ => rename mm into m7 end.
        (* [comment removed for export] *)
        assert (LV6 : rt_live RT S6 = rt_live RT S1)
          by (rewrite LV6r, LV5, <- pm_copy_live_app; exact (pm_copy_roundtrip p1 v1 cv1 cv1' _ ND5 CA1 VD1 ANZ1)).
        lazymatch goal with AGx : agree_on (fun a => aclient (rt_live RT S6) _ _ a /\ outside [(fr + 96, fr + 96 + 8)] a) ?ma ?mb, A6 : ART RT S6 ?mb |- _ =>
          assert (KL10 : keeps_live (rt_live RT S6) ma mb)
            by (eapply keeps_live_of_agree; [exact AGx| intros e He; exact He|];
                intros qq kk xx Hq Hx; cbn [outside]; split; [| exact I];
                exact (chunk_outside_frame RT AF S6 mb fr 1%nat qq kk (fr + 96) (fr + 96 + 8) xx A6
                         ltac:(repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; left; reflexivity)
                         ltac:(lia) ltac:(change (fs_size 1) with 128; lia) Hq Hx));
          pose proof (pix_obj_keep _ ma mb pix v cv (keeps_live_sub _ _ ma mb KL10 ltac:(intros e He; rewrite LV6; exact He)) POBJ9) as POBJ10;
          clear KL10 end.
        clear POBJ9 POBJC9.
        fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; rewrite LV6; exact (SUB01 e He)| solve [frames_sub_tac]| lia]|
                                        cbn [outside]; destruct (NFA _ Hx) as [N1 N2]; split; [lia| exact I]]).
        lazymatch goal with A : ART RT S6 ?mm |- cps _ (ASTA RT S6 _ _) _ =>
          assert (FRS6 : rt_frames RT S6 = (fr, 1%nat) :: rt_frames RT Σ)
            by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity);
          assert (LVP6 : forall p n, In (p, n) (rt_live RT S6) -> 0 < n) by (rewrite LV6; exact LVP1) end.
        clear ND4 ND5 ANZ1 LV5r LV6r.
        hide POBJ10.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
        (* [comment removed for export] *)
        Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_stack_malloc 1%nat; e_pixDeserialize; e_pixDestroy; e_boxCreate; e_pixCopy; e_pixSetSelectCmap; e_boxDestroy; e_pixSetSelectMaskedCmap; 0x8d7a8].
        unfold hid in POBJ10.
        lazymatch goal with A : ART RT ?S ?m0, MUx : munch _ ?m0 ?m1 |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
          assert (KL11 : keeps_live (rt_live RT S) m0 m1)
            by (apply (keeps_live_walk1 RT AF S m0 m1 fr usp (usp + -112) A ltac:(rewrite FRS6; left; reflexivity)
                         ltac:(repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; unfold STACK_WIN; lia) MUx));
          pose proof (pix_obj_keep _ m0 m1 pix v cv (keeps_live_sub (rt_live RT S) _ m0 m1 KL11 ltac:(intros e He; rewrite LV6; exact He)) POBJ10) as POBJ11;
          clear KL11 end.
        clear POBJ10.
        at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                            repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
        eapply cps_seq.
        { eapply CP with (lo := lo) (pixs := pix) (v := v) (cv := cv); rt_side idtac.
          all: lazymatch goal with
               | |- pix_obj ?lv _ _ _ _ => apply (pix_obj_mono _ lv _ _ _ _ ltac:(intros e He; rewrite LV6; exact He) POBJ11)
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- lres _ _ _ _ _ =>
                   unfold lres, RASTER_COST, FRAMES_MAX, LIVE_MAX in *; rewrite FRS6, FR0, LV6; cbn [length];
                   repeat match goal with H : rt_live RT _ = rt_live RT _ |- _ => rewrite H in * end;
                   repeat match goal with H : rt_credit RT _ = _ |- _ => rewrite H in * end;
                   split; [lia| split; [lia| split; [lia| exact LVP1]]]
               | |- ?g => idtac "LEFT-COPY2:" g
               end. }
        Time after_call RT AF.
        (* [comment removed for export] *)
        lazymatch goal with HC : pm_hdr_copy v ?vv cv ?cc |- _ =>
          lazymatch goal with H : pix_obj _ _ ?p vv cc |- _ => rename H into POBJC2; rename HC into HC2; set (p2 := p) in *; set (v2 := vv) in *; set (cv2 := cc) in * end end.
        lazymatch goal with H : p2 <> 0 |- _ => rename H into P2NZ end.
        lazymatch goal with H : rt_live RT ?S = pm_copy_live p2 v2 cv2 (rt_live RT S6) |- _ => rename S into S7; rename H into LV7 end.
        lazymatch goal with |- cps _ (ASTA RT S7 _ (eq (MS _ _ _ _ _ ?mm _))) _ => rename mm into m8 end.
        assert (VD2 : p_data v2 <> 0) by (destruct HC2 as (_ & _ & _ & _ & X & _); exact X).
        rewrite pm_copy_live_app in LV7.
        lazymatch goal with AGx : agree_on (fun a => aclient (rt_live RT S6) _ _ a /\ _) ?ma ?mb |- cps _ (ASTA RT _ _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
          assert (KL12 : keeps_live (rt_live RT S6) ma mb) by (eapply keeps_live_of_agree; [exact AGx| intros e He; exact He| intros; exact I]);
          pose proof (pix_obj_keep _ ma mb pix v cv (keeps_live_sub _ _ ma mb KL12 ltac:(intros e He; rewrite LV6; exact He)) POBJ11) as POBJ12;
          clear KL12 POBJ11 end.
        fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; rewrite LV6; exact (SUB01 e He)| solve [frames_sub_tac]| lia]| exact I]).
        lazymatch goal with A : ART RT S7 ?mm |- cps _ (ASTA RT S7 _ _) _ =>
          assert (FRS7 : rt_frames RT S7 = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity);
          assert (LVP7 : forall p n, In (p, n) (rt_live RT S7) -> 0 < n)
            by (intros p n Hin; rewrite LV7 in Hin; apply in_app_or in Hin; destruct Hin as [Hin|Hin]; [exact (pm_copy_new_pos _ _ _ _ _ POBJC2 VD2 p n Hin)| exact (LVP6 p n Hin)]);
          assert (LEN7 : Z.of_nat (length (rt_live RT S7)) <= Z.of_nat (length (rt_live RT Σ)) + 8)
            by (rewrite LV7, length_app, LV6; pose proof (pm_copy_new_len p2 v2 cv2);
                repeat match goal with H : rt_live RT _ = rt_live RT _ |- _ => rewrite H in * end; lia)
        end.
        hide POBJ12. hide POBJC2.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
        (* [comment removed for export] *)
        Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_stack_malloc 1%nat; e_pixDeserialize; e_pixDestroy; e_boxCreate; e_pixCopy; e_pixSetSelectCmap; e_boxDestroy; e_pixSetSelectMaskedCmap; 0x8d7a8].
        unfold hid in POBJ12, POBJC2.
        lazymatch goal with A : ART RT ?S ?m0, MUx : munch _ ?m0 ?m1 |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
          assert (KL13 : keeps_live (rt_live RT S) m0 m1)
            by (apply (keeps_live_walk1 RT AF S m0 m1 fr usp (usp + -112) A ltac:(rewrite FRS7; left; reflexivity)
                         ltac:(repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; unfold STACK_WIN; lia) MUx));
          pose proof (pix_obj_keep _ m0 m1 pix v cv (keeps_live_sub (rt_live RT S) _ m0 m1 KL13 ltac:(intros e He; rewrite LV7; apply in_or_app; right; rewrite LV6; exact He)) POBJ12) as POBJ13;
          pose proof (pix_obj_keep _ m0 m1 p2 v2 cv2 KL13 POBJC2) as POBJC3; clear KL13 end.
        clear POBJ12 POBJC2.
        at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                            repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
        pose proof MSK as MK. unfold pixSetSelectMaskedCmap_cps in MK.
        eapply cps_seq.
        { eapply MK with (lo := lo) (pix := p2) (v := v2) (cv := cv2); rt_side idtac.
          all: lazymatch goal with
               | |- pix_obj _ _ _ _ _ => exact POBJC3
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- lres _ _ _ _ _ =>
                   unfold lres, RASTER_COST, FRAMES_MAX, LIVE_MAX in *; rewrite FRS7, FR0; cbn [length];
                   split; [lia| split; [lia| split; [repeat match goal with H : rt_credit RT _ = _ |- _ => rewrite H in * end; lia| exact LVP7]]]
               | |- ?g => idtac "LEFT-MSK:" g
               end. }
        Time after_call RT AF.
        lazymatch goal with H : rt_live RT ?S = rt_live RT S7 |- _ => rename S into S8; rename H into LV8 end.
        lazymatch goal with |- cps _ (ASTA RT S8 _ (eq (MS _ _ _ _ _ ?mm _))) _ => rename mm into m10 end.
        lazymatch goal with AGx : agree_on (fun a => aclient (rt_live RT S8) _ _ a /\ _) ?ma ?mb |- cps _ (ASTA RT _ _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
          assert (KL14 : keeps_live (rt_live RT S8) ma mb) by (eapply keeps_live_of_agree; [exact AGx| intros e He; exact He| intros; exact I]);
          pose proof (pix_obj_keep _ ma mb pix v cv (keeps_live_sub _ _ ma mb KL14 ltac:(intros e He; rewrite LV8, LV7; apply in_or_app; right; rewrite LV6; exact He)) POBJ13) as POBJ14;
          pose proof (pix_obj_keep _ ma mb p2 v2 cv2 (keeps_live_sub _ _ ma mb KL14 ltac:(intros e He; rewrite LV8; exact He)) POBJC3) as POBJC4;
          clear KL14 POBJ13 POBJC3 end.
        fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; rewrite LV8, LV7; apply in_or_app; right; rewrite LV6; exact (SUB01 e He)| solve [frames_sub_tac]| lia]| exact I]).
        lazymatch goal with A : ART RT S8 ?mm |- cps _ (ASTA RT S8 _ _) _ =>
          assert (FRS8 : rt_frames RT S8 = (fr, 1%nat) :: rt_frames RT Σ)
            by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity);
          assert (LVP8 : forall p n, In (p, n) (rt_live RT S8) -> 0 < n) by (rewrite LV8; exact LVP7) end.
        lazymatch goal with H : rw_cells asegs _ (fr + 96) [C8 (Z_to_bv 64 p2)] |- _ => rename H into PPC2 end.
        hide POBJ14. hide POBJC4.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
        (* [comment removed for export] *)
        Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_stack_malloc 1%nat; e_pixDeserialize; e_pixDestroy; e_boxCreate; e_pixCopy; e_pixSetSelectCmap; e_boxDestroy; e_pixSetSelectMaskedCmap; 0x8d7a8].
        unfold hid in POBJ14, POBJC4.
        lazymatch goal with A : ART RT ?S ?m0, MUx : munch _ ?m0 ?m1 |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
          assert (KL15 : keeps_live (rt_live RT S) m0 m1)
            by (apply (keeps_live_walk1 RT AF S m0 m1 fr usp (usp + -112) A ltac:(rewrite FRS8; left; reflexivity)
                         ltac:(repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; unfold STACK_WIN; lia) MUx));
          pose proof (pix_obj_keep _ m0 m1 pix v cv (keeps_live_sub (rt_live RT S) _ m0 m1 KL15 ltac:(intros e He; rewrite LV8, LV7; apply in_or_app; right; rewrite LV6; exact He)) POBJ14) as POBJ15;
          pose proof (pix_obj_keep _ m0 m1 p2 v2 cv2 (keeps_live_sub (rt_live RT S) _ m0 m1 KL15 ltac:(intros e He; rewrite LV8; exact He)) POBJC4) as POBJC5; clear KL15 end.
        clear POBJ14 POBJC4.
        pose proof FSH as SHC. split_at SHC 12%nat SHC12. split_at SHC12 1%nat SHC13. clear SHC SHC13.
        pose proof FR as FRrec. split_before FRrec (C8 s0) FRrec15. clear FRrec.
        at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                            repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
        eapply cps_seq.
        { eapply DY with (lo := lo) (pp := fr + 96) (pix := p2) (v := v2) (cv := cv2) (ras := [RA_TOP]); rt_side idtac.
          all: lazymatch goal with
               | |- optrL _ _ _ _ _ _ =>
                   unfold optrL, parked in *; split;
                   [ right; exists fr, 1%nat; rewrite FRS8; change (fs_size 1) with 128;
                     split; [left; reflexivity|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
                     split; [lia|]; split; [lia|];
                     replace (shad (fr + 96)) with (fr / 8 + 2147450892) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
                     destruct SHC12 as [[_ B] _]; exact B
                   | unfold SEGTOP_A; repeat split; first [lia | clear - FR64; Z.div_mod_to_equations; lia] ]
               | |- rw_cells _ _ _ [C8 _] => exact PPC2
               | |- pix_obj ?lv _ _ _ _ => exact (pix_obj_mono _ lv _ _ _ _ ltac:(intros e He; rewrite LV8; exact He) POBJC5)
               | |- uctx _ _ _ _ =>
                   unfold uctx; rewrite !unsigned_lit by lia; unfold parked in S0INV;
                   apply chain_ok_push with (fp1 := bv_unsigned s0);
                     [ lia | clear - SPA; Z.div_mod_to_equations; lia | unfold USTACK_TOP; lia | unfold RA_TOP; lia | apply bv_unsigned_in_range
                     | rewrite Z_to_bv_bv_unsigned; rewrite <- RATOP; rewrite Z_to_bv_bv_unsigned;
                       lazymatch type of FRrec15 with rw_cells _ _ ?a _ => replace (usp + -16) with a by lia end; exact FRrec15
                     | cbn [chain_ok]; unfold link_invalid; lia ]
               | |- Forall _ _ => pose proof tr_destroy as TD; unfold PM_FUZZ_DESTROY_RAS in TD; exact (Forall_inv (Forall_inv_tail TD))
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- lres _ _ _ _ _ =>
                   unfold lres, RASTER_COST, FRAMES_MAX, LIVE_MAX in *; rewrite FRS8, FR0; cbn [length];
                   split; [lia| split; [rewrite LV8; lia|
                   split; [repeat match goal with H : rt_credit RT _ = _ |- _ => rewrite H in * end; lia| exact LVP8]]]
               | |- ?g => idtac "LEFT-DY2:" g
               end. }
        clear SHC12.
        assert (ANZ2 : p_cmap v2 <> 0 -> c_arr cv2 <> 0)
          by (intros NZ; destruct POBJC5 as (_ & _ & _ & _ & [CZ|((_ & _ & (_ & A0 & _) & _) & _)]); [contradiction| lia]).
        lazymatch goal with A : ART RT S8 ?mm |- _ =>
          assert (ND8 : List.NoDup (map fst (pm_copy_live p2 v2 cv2 (rt_live RT S6))))
            by (pose proof (live_nodup RT AF S8 mm A LVP8) as ND; rewrite LV8, LV7 in ND; rewrite pm_copy_live_app; exact ND) end.
        Time after_call RT AF.
        lazymatch goal with H : rt_live RT ?S = live_destroy p2 v2 cv2 (rt_live RT S8) |- _ => rename S into S9; rename H into LV9r end.
        lazymatch goal with |- cps _ (ASTA RT S9 _ (eq (MS _ _ _ _ _ ?mm _))) _ => rename mm into m11 end.
        assert (LV9 : rt_live RT S9 = rt_live RT S1)
          by (rewrite LV9r, LV8, LV7, <- pm_copy_live_app, (pm_copy_roundtrip p2 v2 cv2 cv2 _ ND8 eq_refl VD2 ANZ2); exact LV6).
        lazymatch goal with AGx : agree_on (fun a => aclient (rt_live RT S9) _ _ a /\ outside [(fr + 96, fr + 96 + 8)] a) ?ma ?mb, A9 : ART RT S9 ?mb |- _ =>
          assert (KL16 : keeps_live (rt_live RT S9) ma mb)
            by (eapply keeps_live_of_agree; [exact AGx| intros e He; exact He|];
                intros qq kk xx Hq Hx; cbn [outside]; split; [| exact I];
                exact (chunk_outside_frame RT AF S9 mb fr 1%nat qq kk (fr + 96) (fr + 96 + 8) xx A9
                         ltac:(repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; left; reflexivity)
                         ltac:(lia) ltac:(change (fs_size 1) with 128; lia) Hq Hx));
          pose proof (pix_obj_keep _ ma mb pix v cv (keeps_live_sub _ _ ma mb KL16 ltac:(intros e He; rewrite LV9; exact He)) POBJ15) as POBJ16;
          clear KL16 end.
        clear POBJ15 POBJC5.
        fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; rewrite LV9; exact (SUB01 e He)| solve [frames_sub_tac]| lia]|
                                        cbn [outside]; destruct (NFA _ Hx) as [N1 N2]; split; [lia| exact I]]).
        lazymatch goal with A : ART RT S9 ?mm |- cps _ (ASTA RT S9 _ _) _ =>
          assert (FRS9 : rt_frames RT S9 = (fr, 1%nat) :: rt_frames RT Σ)
            by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity);
          assert (LVP9 : forall p n, In (p, n) (rt_live RT S9) -> 0 < n) by (rewrite LV9; exact LVP1) end.
        clear ND8 ANZ2 LV9r.
        hide POBJ16.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
        (* [comment removed for export] *)
        Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_stack_malloc 1%nat; e_pixDeserialize; e_pixDestroy; e_boxCreate; e_pixCopy; e_pixSetSelectCmap; e_boxDestroy; e_pixSetSelectMaskedCmap; 0x8d7a8].
        unfold hid in POBJ16.
        lazymatch goal with A : ART RT ?S ?m0, MUx : munch _ ?m0 ?m1 |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
          assert (KL17 : keeps_live (rt_live RT S) m0 m1)
            by (apply (keeps_live_walk1 RT AF S m0 m1 fr usp (usp + -112) A ltac:(rewrite FRS9; left; reflexivity)
                         ltac:(repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; unfold STACK_WIN; lia) MUx));
          pose proof (pix_obj_keep _ m0 m1 pix v cv (keeps_live_sub (rt_live RT S) _ m0 m1 KL17 ltac:(intros e He; rewrite LV9; exact He)) POBJ16) as POBJ17;
          clear KL17 end.
        clear POBJ16.
        split_at FRM 4%nat FRMp. split_at FRMp 1%nat FRMq.
        pose proof FSH as SHC. split_at SHC 4%nat SHC4. split_at SHC4 1%nat SHC5. clear SHC SHC5.
        pose proof FR as FRrec. split_before FRrec (C8 s0) FRrec17. clear FRrec.
        at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                            repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
        eapply cps_seq.
        { eapply DY with (lo := lo) (pp := fr + 32) (pix := pix) (v := v) (cv := cv) (ras := [RA_TOP]); rt_side idtac.
          all: lazymatch goal with
               | |- optrL _ _ _ _ _ _ =>
                   unfold optrL, parked in *; split;
                   [ right; exists fr, 1%nat; rewrite FRS9; change (fs_size 1) with 128;
                     split; [left; reflexivity|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
                     split; [lia|]; split; [lia|];
                     replace (shad (fr + 32)) with (fr / 8 + 2147450884) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
                     destruct SHC4 as [[_ B] _]; exact B
                   | unfold SEGTOP_A; repeat split; first [lia | clear - FR64; Z.div_mod_to_equations; lia] ]
               | |- rw_cells _ _ _ [C8 _] => exact FRMp
               | |- pix_obj ?lv _ _ _ _ => exact (pix_obj_mono _ lv _ _ _ _ ltac:(intros e He; rewrite LV9; exact He) POBJ17)
               | |- uctx _ _ _ _ =>
                   unfold uctx; rewrite !unsigned_lit by lia; unfold parked in S0INV;
                   apply chain_ok_push with (fp1 := bv_unsigned s0);
                     [ lia | clear - SPA; Z.div_mod_to_equations; lia | unfold USTACK_TOP; lia | unfold RA_TOP; lia | apply bv_unsigned_in_range
                     | rewrite Z_to_bv_bv_unsigned; rewrite <- RATOP; rewrite Z_to_bv_bv_unsigned;
                       lazymatch type of FRrec17 with rw_cells _ _ ?a _ => replace (usp + -16) with a by lia end; exact FRrec17
                     | cbn [chain_ok]; unfold link_invalid; lia ]
               | |- Forall _ _ => pose proof tr_destroy as TD; unfold PM_FUZZ_DESTROY_RAS in TD; exact (Forall_inv (Forall_inv_tail (Forall_inv_tail TD)))
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- lres _ _ _ _ _ =>
                   unfold lres, RASTER_COST, FRAMES_MAX, LIVE_MAX in *; rewrite FRS9, FR0; cbn [length];
                   split; [lia| split; [rewrite LV9; repeat match goal with H : rt_live RT _ = rt_live RT _ |- _ => rewrite H in * end; lia|
                   split; [repeat match goal with H : rt_credit RT _ = _ |- _ => rewrite H in * end; lia| exact LVP9]]]
               | |- ?g => idtac "LEFT-DY3:" g
               end. }
        clear SHC4.
        Time after_call RT AF.
        lazymatch goal with H : rt_live RT ?S = live_destroy pix v cv (rt_live RT S9) |- _ => rename S into S10; rename H into LV10r end.
        lazymatch goal with |- cps _ (ASTA RT S10 _ (eq (MS _ _ _ _ _ ?mm _))) _ => rename mm into m12 end.
        (* [comment removed for export] *)
        assert (LV10 : rt_live RT S10 = rt_live RT Σ)
          by (rewrite LV10r, LV9, LVE; repeat match goal with H : rt_live RT _ = rt_live RT Σ |- _ => rewrite H end; reflexivity).
        clear POBJ17.
        fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; rewrite LV10; exact He| solve [frames_sub_tac]| lia]|
                                        cbn [outside]; destruct (NFA _ Hx) as [N1 N2]; split; [lia| exact I]]).
        clear LV10r PIN IN.
        (* [comment removed for export] *)
        repeat match goal with H : rw_cells asegs _ (usp + -16) _ |- _ => clear H end.
        repeat match goal with H : rw_cells asegs _ (fr + _) _ |- _ => clear H end.
        repeat match goal with H : ART RT _ ?mm |- cps _ (ASTA RT _ _ (eq (MS _ _ _ _ _ ?mc _))) _ => lazymatch mm with mc => fail | m => fail | _ => clear H end end.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
        (* [comment removed for export] *)
        Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_stack_malloc 1%nat; e_pixDeserialize; e_pixDestroy; e_boxCreate; e_pixCopy; e_pixSetSelectCmap; e_boxDestroy; e_pixSetSelectMaskedCmap; 0x8d7a8].
        Time frame_release_g RT AF GP MST Σ fr 1%nat 128 PF AGF PFS usp lo 0x8d7b0
          ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
          ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                            repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia])
          ltac:(fun Hx => exact (proj1 Hx)) ltac:(fun fl FLN => idtac).
        refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
        Time walk_to AF MST [(usp - 112, usp)] (@nil Z).
        try (lazymatch goal with ST' : stk asegs _ lo (usp + -112) |- _ => release_frame FR ST' usp end).   (* [comment removed for export] *)
        cps_stop.
        apply cps_finish; intros c Hc; subst QF; cbv beta.
        lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S end.
        split; [| unfold RASTER_COST in *; alg_tac].
        eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-; eexists.
        split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
        split; [split; [assumption| split; assumption]|].
        split; [intros a Ha Ho; exact (AGF a (conj Ha Ho))|].
        lazymatch goal with LHx : LIBH ?mm |- LIB ?mm => destruct LHx as (LH0 & LHH); split; [exact LH0| eexists; exact LHH] end.
Qed.
End PMFUZZ.
