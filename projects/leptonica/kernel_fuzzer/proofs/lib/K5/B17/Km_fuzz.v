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
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.B17 Require Import Layout.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.B17 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit Lept_chain Lept_leaf LeptC_leaf Lept_objkit Km_setelem Km_iface Km_kit KmF_kit Km_walkkit.
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
Lemma tr_destroy : Forall (fun f => In [f; RA_FUZZ_DESTROY; RA_TOP] CLIENT_TRACES) DESTROY_FREE_RAS.
Proof.
  apply Forall_forall. intros f Hf. unfold DESTROY_FREE_RAS in Hf. cbn [In] in Hf.
  destruct Hf as [<-|[<-|[]]]; vm_compute; tauto.
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
      assert (E1 := rw_cells_agree_nw asegs mm m' _ _ D1 (static_agree RT GP client_static mm m' AGS (fun a Ha => Ha) 0xcf180 4 ltac:(cbn; tauto)));
      assert (E2 := rw_cells_agree_nw asegs mm m' _ _ D2 (static_agree RT GP client_static mm m' AGS (fun a Ha => Ha) 0xcf1c0 8 ltac:(cbn; tauto)));
      assert (E3 := rw_cells_agree_nw asegs mm m' _ _ D3 (static_agree RT GP client_static mm m' AGS (fun a Ha => Ha) 0xcf1e0 8 ltac:(cbn; tauto)));
      assert (E4 := rw_cells_agree_nw asegs mm m' _ _ D4 (static_agree RT GP client_static mm m' AGS (fun a Ha => Ha) 0xcf1a0 8 ltac:(cbn; tauto)));
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

Section KMFUZZ.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis DESER : pixDeserialize_cps RT.
Hypothesis DESTROY : pixDestroy_cps RT.
Hypothesis KFP : kernelCreateFromPix_cps RT.
Hypothesis KD : kernelDestroy_cps RT.

Theorem km_fuzz_ok : km_fuzz_one_cps RT.
Proof using AF RC GP DESER DESTROY KFP KD.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d bs lo
    FDO MST -> -> -> RATOP DPOS BSL BYTES OWN FR0 LVP LVB CRB SECB S0INV LIBm SSP ART0 MI ST LOW LOR SPT SPA SPB.
  destruct LIBm as ((LSEV & LALLOC & LDEALLOC) & (h0 & LHAND)).
  unfold g_LeptMsgSeverity, g_pix_alloc, g_pix_dealloc, g_stderr_handler in *. clear BYTES.
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, e_km_fuzz, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold FUZZ_STACK, FUZZ_COST, KM_FUZZ_LIVE, KM_FUZZ_SECB, LSTK, STDERR_STACK, RASTER_COST in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
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
    walk_to AF MST [(usp - 96, usp)] [e_stack_malloc 1%nat; e_pixDeserialize; e_pixDestroy; e_kernelCreateFromPix; e_kernelDestroy; 0x8cdf0].
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
      walk_to AF MST [(usp - 96, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_stack_malloc 1%nat; e_pixDeserialize; e_pixDestroy; e_kernelCreateFromPix; e_kernelDestroy; 0x8cdf0].
      frame_release_raw RT AF GP MST Σ fr 1%nat 128 PF AGF PFS usp lo 0x8cdf8
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
      walk_to AF MST [(usp - 96, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16); (848288, 848296)]
                   [e_stack_malloc 1%nat; e_pixDeserialize; e_pixDestroy; e_kernelCreateFromPix; e_kernelDestroy; 0x8cdf0].
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
        - unfold RASTER_COST. lres_tac.
        - repeat match goal with H : rt_live RT _ = _ |- _ => rewrite H end; lia. }
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
        walk_to AF MST [(usp - 96, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_stack_malloc 1%nat; e_pixDeserialize; e_pixDestroy; e_kernelCreateFromPix; e_kernelDestroy; 0x8cdf0].
        frame_release_g RT AF GP MST Σ fr 1%nat 128 PF AGF PFS usp lo 0x8cdf8
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
        lazymatch type of LVE with live_destroy _ _ _ (rt_live RT ?S) = rt_live RT ?S0 => rename S into S1; rename S0 into S0f end.
        lazymatch goal with H : rt_live RT S0f = rt_live RT Σ |- _ => rename H into LV0f end.
        unfold hid in POBJ.
        pose proof POBJ as (_ & _ & (HD1 & HW1 & HH1 & HWPL & HRS) & _).
        assert (WH8 : p_d v = 8 -> p_w v * p_h v <= 0x4000000)
          by (intros D8; rewrite D8 in HWPL; clear - HWPL HRS HW1 HH1; Z.div_mod_to_equations; nia).
        hide POBJ.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
        (* [comment removed for export] *)
        Time walk_to AF MST [(usp - 96, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_stack_malloc 1%nat; e_pixDeserialize; e_pixDestroy; e_kernelCreateFromPix; e_kernelDestroy; 0x8cdf0].
        assert (ND1 : List.NoDup (map fst (rt_live RT S1)))
          by (lazymatch goal with A : ART RT S1 ?mm |- _ => exact (live_nodup RT AF S1 mm A LVP1) end).
        unfold hid in POBJ.
        assert (SECP : sec_bytes (rt_live RT S1) <= sec_bytes (rt_live RT Σ) + 0x4000000)
          by (pose proof (pix_destroy_sec (rt_live RT S1) _ pix v cv ND1 POBJ VDATA) as X; rewrite LVE, LV0f in X; exact X).
        hide POBJ.
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
        pose proof KFP as KF. unfold kernelCreateFromPix_cps in KF.
        eapply cps_seq.
        { eapply KF with (lo := lo) (pix := pix) (v := v) (cv := cv); rt_side idtac.
          all: lazymatch goal with
               | |- pix_obj _ _ _ _ _ => exact POBJ1
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- lres _ _ _ _ _ =>
                   unfold lres, RASTER_COST, FRAMES_MAX, LIVE_MAX in *; rewrite FRSh, FR0; cbn [length];
                   rewrite LV0f in LEN1;
                   repeat match goal with H : rt_credit RT _ = _ |- _ => rewrite H in * end;
                   split; [lia| split; [lia| split; [lia| exact LVP1]]]
               | |- p_d _ = 8 -> _ => intros D8; pose proof (WH8 D8); lia
               | |- ?g => idtac "LEFT-KFP:" g
               end. }
        Time after_call RT AF.
        fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [exact SUB01| solve [frames_sub_tac]| lia]| exact I]).
        lazymatch goal with H : ?k = 0 -> rt_live RT ?S = rt_live RT S1 |- _ => rename S into S2; rename H into LVZ2; set (kel := k) in * end.
        lazymatch goal with H : pix_obj (rt_live RT S2) _ pix v cv |- _ => rename H into POBJ2 end.
        lazymatch goal with H : kel = 0 \/ _ |- _ => rename H into KOR end.
        lazymatch goal with H : rt_frames RT S2 = rt_frames RT S1 |- _ => rename H into FRS2 end.
        lazymatch goal with H : rt_sp0 RT S2 = rt_sp0 RT S1 |- _ => rename H into SP2 end.
        lazymatch goal with H : rt_credit RT S1 - 2 ^ 30 <= rt_credit RT S2 |- _ => rename H into CR2 end.
        lazymatch goal with |- cps _ (ASTA RT S2 _ (eq (MS _ _ _ _ _ ?mm _))) _ => rename mm into m4 end.
        lazymatch goal with A : ART RT S2 m4 |- _ => rename A into ART2 end.
        assert (FRS2' : rt_frames RT S2 = (fr, 1%nat) :: rt_frames RT Σ) by (rewrite FRS2; exact FRSh).
        assert (LVP2 : forall p n, In (p, n) (rt_live RT S2) -> 0 < n).
        { destruct KOR as [KZ|(data & rows & D8 & KOBJ & LV2)]; [rewrite (LVZ2 KZ); exact LVP1|].
          rewrite LV2. intros p n Hin. apply km_live_inv in Hin as [Hin|Hin]; [| exact (LVP1 p n Hin)].
          unfold km_chunks in Hin. destruct KOBJ as (_ & _ & _ & _ & _ & _ & _ & SYB & SXB).
          destruct Hin as [E|[E|Hin]]; [injection E as <- <-; lia| injection E as <- <-; lia|].
          apply in_map_iff in Hin as (r & E & _). injection E as <- <-. lia. }
        pose proof DESTROY as DY. unfold pixDestroy_cps in DY.
        destruct KOR as [KZ|(data & rows & D8 & KOBJ & LV2)].
        -- (* [comment removed for export] *)
          pose proof (LVZ2 KZ) as LV2. clear LVZ2.
          hide POBJ2.
          refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
          (* [comment removed for export] *)
          Time walk_to AF MST [(usp - 96, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_stack_malloc 1%nat; e_pixDeserialize; e_pixDestroy; e_kernelCreateFromPix; e_kernelDestroy; 0x8cdf0].
          unfold hid in POBJ2.
          lazymatch goal with A : ART RT ?S ?m0, MUx : munch _ ?m0 ?m1 |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
            assert (KL3 : keeps_live (rt_live RT S) m0 m1)
              by (apply (keeps_live_walk1 RT AF S m0 m1 fr usp (usp + -96) A ltac:(rewrite FRS2'; left; reflexivity)
                           ltac:(repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; unfold STACK_WIN; lia) MUx));
            pose proof (pix_obj_keep _ m0 m1 pix v cv KL3 POBJ2) as POBJ3; clear KL3 end.
          clear POBJ2.
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
                     [ right; exists fr, 1%nat; rewrite FRS2'; change (fs_size 1) with 128;
                       split; [left; reflexivity|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
                       split; [lia|]; split; [lia|];
                       replace (shad (fr + 32)) with (fr / 8 + 2147450884) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
                       destruct SHC4 as [[_ B] _]; exact B
                     | unfold SEGTOP_A; repeat split; first [lia | clear - FR64; Z.div_mod_to_equations; lia] ]
                 | |- rw_cells _ _ _ [C8 _] => exact FRMp
                 | |- pix_obj _ _ _ _ _ => exact POBJ3
                 | |- uctx _ _ _ _ =>
                     unfold uctx; rewrite !unsigned_lit by lia; unfold parked in S0INV;
                     apply chain_ok_push with (fp1 := bv_unsigned s0);
                       [ lia | clear - SPA; Z.div_mod_to_equations; lia | unfold USTACK_TOP; lia | unfold RA_TOP; lia | apply bv_unsigned_in_range
                       | rewrite Z_to_bv_bv_unsigned; rewrite <- RATOP; rewrite Z_to_bv_bv_unsigned;
                         lazymatch type of FRrec17 with rw_cells _ _ ?a _ => replace (usp + -16) with a by lia end; exact FRrec17
                       | cbn [chain_ok]; unfold link_invalid; lia ]
                 | |- Forall _ _ => exact tr_destroy
                 | |- lenv _ _ _ _ _ _ => lenv_tac
                 | |- lres _ _ _ _ _ =>
                     unfold lres, RASTER_COST, FRAMES_MAX, LIVE_MAX in *; rewrite FRS2', FR0; cbn [length]; rewrite LV2;
                     split; [lia| split; [rewrite LV0f in LEN1; lia| split; [repeat match goal with H : rt_credit RT _ = _ |- _ => rewrite H in * end; lia| exact LVP1]]]
                 | |- ?g => idtac "LEFT-DY:" g
                 end. }
          clear SHC4.
          Time after_call RT AF.
          lazymatch goal with H : rt_live RT ?S = live_destroy pix v cv (rt_live RT S2) |- _ => rename S into S3; rename H into LV3r end.
          lazymatch goal with |- cps _ (ASTA RT S3 _ (eq (MS _ _ _ _ _ ?mm _))) _ => rename mm into m5 end.
          assert (LV3 : rt_live RT S3 = rt_live RT Σ) by (rewrite LV3r, LV2, LVE, LV0f; reflexivity).
          clear POBJ3.
          fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; rewrite LV3; exact He| solve [frames_sub_tac]| lia]|
                                          cbn [outside]; destruct (NFA _ Hx) as [N1 N2]; split; [lia| exact I]]).
          lazymatch goal with H : rt_frames RT S3 = rt_frames RT S2 |- _ => assert (FRS3 : rt_frames RT S3 = (fr, 1%nat) :: rt_frames RT Σ) by (rewrite H; exact FRS2') end.
          assert (LVP3 : forall p n, In (p, n) (rt_live RT S3) -> 0 < n) by (rewrite LV3; exact LVP).
          refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
          (* [comment removed for export] *)
          Time walk_to AF MST [(usp - 96, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_stack_malloc 1%nat; e_pixDeserialize; e_pixDestroy; e_kernelCreateFromPix; e_kernelDestroy; 0x8cdf0].
          split_at FRMq 1%nat FRMk. split_at FRMk 1%nat FRMl.
          pose proof FSH as SHC. split_at SHC 8%nat SHC8. split_at SHC8 1%nat SHC9. clear SHC SHC9.
          at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                        ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                              repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
          pose proof KD as KDc. unfold kernelDestroy_cps in KDc.
          eapply cps_seq.
          { eapply KDc with (lo := lo) (pp := fr + 64) (kel := kel) (sy := 0) (sx := 0) (cy := 0) (cx := 0) (data := 0) (rows := []); rt_side idtac.
            all: lazymatch goal with
                 | |- optrF _ _ _ _ _ =>
                     unfold optrF, parked in *; split;
                     [ exists fr, 1%nat; rewrite FRS3; change (fs_size 1) with 128;
                       split; [left; reflexivity|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
                       split; [lia|]; split; [lia|];
                       replace (shad (fr + 64)) with (fr / 8 + 2147450888) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
                       destruct SHC8 as [[_ B] _]; exact B
                     | unfold SEGTOP_A; repeat split; first [lia | clear - FR64; Z.div_mod_to_equations; lia] ]
                 | |- rw_cells _ _ _ [C8 _] => exact FRMk
                 | |- _ = 0 \/ _ => left; exact KZ
                 | |- lenv _ _ _ _ _ _ => lenv_tac
                 | |- lres _ _ _ _ _ =>
                     unfold lres, RASTER_COST, FRAMES_MAX, LIVE_MAX in *; rewrite FRS3, FR0, LV3; cbn [length];
                     split; [lia| split; [lia| split; [repeat match goal with H : rt_credit RT _ = _ |- _ => rewrite H in * end; lia| exact LVP]]]
                 | |- ?g => idtac "LEFT-KD:" g
                 end. }
          clear SHC8.
          Time after_call RT AF.
          lazymatch goal with H : rt_live RT ?S = (if kel =? 0 then rt_live RT S3 else _) |- _ => rename S into S4; rename H into LV4r end.
          assert (LV4 : rt_live RT S4 = rt_live RT Σ) by (rewrite LV4r, KZ; cbn; exact LV3).
          fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; rewrite LV4; exact He| solve [frames_sub_tac]| lia]|
                                          cbn [outside]; destruct (NFA _ Hx) as [N1 N2]; split; [lia| exact I]]).
          clear LV4r LV3r PIN IN.
          (* [comment removed for export] *)
          repeat match goal with H : rw_cells asegs _ (usp + -16) _ |- _ => clear H end.
          repeat match goal with H : rw_cells asegs _ (fr + _) _ |- _ => clear H end.
          repeat match goal with H : ART RT _ ?mm |- cps _ (ASTA RT _ _ (eq (MS _ _ _ _ _ ?mc _))) _ => lazymatch mm with mc => fail | m => fail | _ => clear H end end.
          refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
          (* [comment removed for export] *)
          Time walk_to AF MST [(usp - 96, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_stack_malloc 1%nat; e_pixDeserialize; e_pixDestroy; e_kernelCreateFromPix; e_kernelDestroy; 0x8cdf0].
          Time frame_release_g RT AF GP MST Σ fr 1%nat 128 PF AGF PFS usp lo 0x8cdf8
            ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
            ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                              repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia])
            ltac:(fun Hx => exact (proj1 Hx)) ltac:(fun fl FLN => idtac).
          refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
          Time walk_to AF MST [(usp - 96, usp)] (@nil Z).
          try (lazymatch goal with ST' : stk asegs _ lo (usp + -96) |- _ => release_frame FR ST' usp end).
          cps_stop.
          apply cps_finish; intros c Hc; subst QF; cbv beta.
          lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S end.
          split; [| unfold RASTER_COST in *; alg_tac].
          eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-; eexists.
          split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
          split; [split; [assumption| split; assumption]|].
          split; [intros a Ha Ho; exact (AGF a (conj Ha Ho))|].
          lazymatch goal with LHx : LIBH ?mm |- LIB ?mm => destruct LHx as (LH0 & LHH); split; [exact LH0| eexists; exact LHH] end.
        -- (* [comment removed for export] *)
          assert (ND2 : List.NoDup (map fst (km_live kel data (p_h v) (p_w v) rows (rt_live RT S1))))
            by (lazymatch goal with A : ART RT S2 ?mm |- _ => pose proof (live_nodup RT AF S2 mm A LVP2) as ND; rewrite LV2 in ND; exact ND end).
          hide POBJ2. hide KOBJ.
          refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
          (* [comment removed for export] *)
          Time walk_to AF MST [(usp - 96, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_stack_malloc 1%nat; e_pixDeserialize; e_pixDestroy; e_kernelCreateFromPix; e_kernelDestroy; 0x8cdf0].
          unfold hid in POBJ2, KOBJ.
          lazymatch goal with A : ART RT ?S ?m0, MUx : munch _ ?m0 ?m1 |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
            assert (KL3 : keeps_live (rt_live RT S) m0 m1)
              by (apply (keeps_live_walk1 RT AF S m0 m1 fr usp (usp + -96) A ltac:(rewrite FRS2'; left; reflexivity)
                           ltac:(repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; unfold STACK_WIN; lia) MUx));
            pose proof (pix_obj_keep _ m0 m1 pix v cv KL3 POBJ2) as POBJ3;
            pose proof (kel_obj_keep _ m0 m1 kel (p_h v) (p_w v) 2 2 data rows KL3 KOBJ) as KOBJ3; clear KL3 end.
          clear POBJ2 KOBJ.
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
                     [ right; exists fr, 1%nat; rewrite FRS2'; change (fs_size 1) with 128;
                       split; [left; reflexivity|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
                       split; [lia|]; split; [lia|];
                       replace (shad (fr + 32)) with (fr / 8 + 2147450884) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
                       destruct SHC4 as [[_ B] _]; exact B
                     | unfold SEGTOP_A; repeat split; first [lia | clear - FR64; Z.div_mod_to_equations; lia] ]
                 | |- rw_cells _ _ _ [C8 _] => exact FRMp
                 | |- pix_obj _ _ _ _ _ => exact POBJ3
                 | |- uctx _ _ _ _ =>
                     unfold uctx; rewrite !unsigned_lit by lia; unfold parked in S0INV;
                     apply chain_ok_push with (fp1 := bv_unsigned s0);
                       [ lia | clear - SPA; Z.div_mod_to_equations; lia | unfold USTACK_TOP; lia | unfold RA_TOP; lia | apply bv_unsigned_in_range
                       | rewrite Z_to_bv_bv_unsigned; rewrite <- RATOP; rewrite Z_to_bv_bv_unsigned;
                         lazymatch type of FRrec17 with rw_cells _ _ ?a _ => replace (usp + -16) with a by lia end; exact FRrec17
                       | cbn [chain_ok]; unfold link_invalid; lia ]
                 | |- Forall _ _ => exact tr_destroy
                 | |- lenv _ _ _ _ _ _ => lenv_tac
                 | |- lres _ _ _ _ _ =>
                     unfold lres, RASTER_COST, FRAMES_MAX, LIVE_MAX in *; rewrite FRS2', FR0; cbn [length];
                     split; [lia| split; [rewrite LV2, km_live_length; destruct KOBJ3 as (_ & _ & _ & _ & KLEN & _); rewrite KLEN; rewrite LV0f in LEN1; lia|
                     split; [repeat match goal with H : rt_credit RT _ = _ |- _ => rewrite H in * end; lia| exact LVP2]]]
                 | |- ?g => idtac "LEFT-DY:" g
                 end. }
          clear SHC4.
          Time after_call RT AF.
          lazymatch goal with H : rt_live RT ?S = live_destroy pix v cv (rt_live RT S2) |- _ => rename S into S3; rename H into LV3r end.
          lazymatch goal with |- cps _ (ASTA RT S3 _ (eq (MS _ _ _ _ _ ?mm _))) _ => rename mm into m5 end.
          assert (LV3 : rt_live RT S3 = km_live kel data (p_h v) (p_w v) rows (rt_live RT Σ))
            by (rewrite LV3r, LV2, (live_destroy_km kel data (p_h v) (p_w v) rows (rt_live RT S1) _ pix v cv ND2 POBJ1), LVE, LV0f; reflexivity).
          lazymatch goal with AGx : agree_on (fun a => aclient (rt_live RT S3) _ _ a /\ outside [(fr + 32, fr + 32 + 8)] a) ?ma ?mb, A3 : ART RT S3 ?mb |- _ =>
            assert (KL5 : keeps_live (rt_live RT S3) ma mb)
              by (eapply keeps_live_of_agree; [exact AGx| intros e He; exact He|];
                  intros qq kk xx Hq Hx; cbn [outside]; split; [| exact I];
                  let FLV := fresh "FLV" in
                  pose proof (af_frames_range RT AF S3 mb fr 1%nat A3
                                ltac:(repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; left; reflexivity)) as (_ & _ & _ & FLV);
                  specialize (FLV qq kk Hq); change (fs_size 1) with 128 in FLV; lia);
            assert (KOBJ4 : kel_obj (rt_live RT S3) mb kel (p_h v) (p_w v) 2 2 data rows)
              by (apply (kel_obj_keep _ ma mb kel (p_h v) (p_w v) 2 2 data rows KL5);
                  apply (kel_obj_move (rt_live RT S2)); [| exact KOBJ3];
                  intros e He; rewrite LV3; destruct He as [<-|[<-|He]];
                  [ apply km_live_in_kel | apply km_live_in_data | apply in_map_iff in He as (r & <- & Hr); apply km_live_in_row; exact Hr ]);
            clear KL5 end.
          clear POBJ3 KOBJ3.
          fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; rewrite LV3; apply km_live_in_old; exact He| solve [frames_sub_tac]| lia]|
                                          cbn [outside]; destruct (NFA _ Hx) as [N1 N2]; split; [lia| exact I]]).
          lazymatch goal with H : rt_frames RT S3 = rt_frames RT S2 |- _ => assert (FRS3 : rt_frames RT S3 = (fr, 1%nat) :: rt_frames RT Σ) by (rewrite H; exact FRS2') end.
          assert (LVP3 : forall p n, In (p, n) (rt_live RT S3) -> 0 < n)
            by (intros p n Hin; rewrite LV3r in Hin; apply live_destroy_sub in Hin; exact (LVP2 p n Hin)).
          hide KOBJ4.
          refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
          (* [comment removed for export] *)
          Time walk_to AF MST [(usp - 96, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_stack_malloc 1%nat; e_pixDeserialize; e_pixDestroy; e_kernelCreateFromPix; e_kernelDestroy; 0x8cdf0].
          unfold hid in KOBJ4.
          try (lazymatch goal with A : ART RT ?S ?m0, MUx : munch _ ?m0 ?m1 |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
            assert (KL6 : keeps_live (rt_live RT S) m0 m1)
              by (apply (keeps_live_walk1 RT AF S m0 m1 fr usp (usp + -96) A ltac:(rewrite FRS3; left; reflexivity)
                           ltac:(repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; unfold STACK_WIN; lia) MUx));
            pose proof (kel_obj_keep _ m0 m1 kel (p_h v) (p_w v) 2 2 data rows KL6 KOBJ4) as KOBJ5; clear KL6 KOBJ4 end).
          try (rename KOBJ4 into KOBJ5).
          split_at FRMq 1%nat FRMk. split_at FRMk 1%nat FRMl.
          pose proof FSH as SHC. split_at SHC 8%nat SHC8. split_at SHC8 1%nat SHC9. clear SHC SHC9.
          at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                        ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                              repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
          pose proof KD as KDc. unfold kernelDestroy_cps in KDc.
          eapply cps_seq.
          { eapply KDc with (lo := lo) (pp := fr + 64) (kel := kel) (sy := p_h v) (sx := p_w v) (cy := 2) (cx := 2) (data := data) (rows := rows); rt_side idtac.
            all: lazymatch goal with
                 | |- optrF _ _ _ _ _ =>
                     unfold optrF, parked in *; split;
                     [ exists fr, 1%nat; rewrite FRS3; change (fs_size 1) with 128;
                       split; [left; reflexivity|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
                       split; [lia|]; split; [lia|];
                       replace (shad (fr + 64)) with (fr / 8 + 2147450888) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
                       destruct SHC8 as [[_ B] _]; exact B
                     | unfold SEGTOP_A; repeat split; first [lia | clear - FR64; Z.div_mod_to_equations; lia] ]
                 | |- rw_cells _ _ _ [C8 _] => exact FRMk
                 | |- _ = 0 \/ _ => right; exact KOBJ5
                 | |- lenv _ _ _ _ _ _ => lenv_tac
                 | |- lres _ _ _ _ _ =>
                     unfold lres, RASTER_COST, FRAMES_MAX, LIVE_MAX in *; rewrite FRS3, FR0; cbn [length];
                     split; [lia| split; [rewrite LV3, km_live_length; destruct KOBJ5 as (_ & _ & _ & _ & KLEN & _); rewrite KLEN; lia|
                     split; [repeat match goal with H : rt_credit RT _ = _ |- _ => rewrite H in * end; lia| exact LVP3]]]
                 | |- ?g => idtac "LEFT-KD:" g
                 end. }
          assert (KNZ : kel <> 0) by (destruct KOBJ5 as (_ & (_ & K0 & _) & _); lia).
          lazymatch goal with A : ART RT S3 ?mm |- _ =>
            pose proof (live_nodup RT AF S3 mm A LVP3) as KND0; rewrite LV3 in KND0;
            destruct (km_live_nodup_split kel data (p_h v) (p_w v) rows (rt_live RT Σ) KND0) as [KND NIN]; clear KND0 end.
          clear SHC8 KOBJ5.
          Time after_call RT AF.
          lazymatch goal with H : rt_live RT ?S = (if kel =? 0 then rt_live RT S3 else _) |- _ => rename S into S4; rename H into LV4r end.
          assert (LV4 : rt_live RT S4 = rt_live RT Σ)
            by (rewrite LV4r; replace (kel =? 0) with false by (symmetry; apply Z.eqb_neq; exact KNZ); rewrite LV3;
                exact (km_unlive_live kel data (p_h v) (p_w v) rows (rt_live RT Σ) KND NIN)).
          fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; rewrite LV4; exact He| solve [frames_sub_tac]| lia]|
                                          cbn [outside]; destruct (NFA _ Hx) as [N1 N2]; split; [lia| exact I]]).
          clear LV4r LV3r PIN IN KND NIN ND2.
          (* [comment removed for export] *)
          repeat match goal with H : rw_cells asegs _ (usp + -16) _ |- _ => clear H end.
          repeat match goal with H : rw_cells asegs _ (fr + _) _ |- _ => clear H end.
          repeat match goal with H : ART RT _ ?mm |- cps _ (ASTA RT _ _ (eq (MS _ _ _ _ _ ?mc _))) _ => lazymatch mm with mc => fail | m => fail | _ => clear H end end.
          refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
          (* [comment removed for export] *)
          Time walk_to AF MST [(usp - 96, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_stack_malloc 1%nat; e_pixDeserialize; e_pixDestroy; e_kernelCreateFromPix; e_kernelDestroy; 0x8cdf0].
          Time frame_release_g RT AF GP MST Σ fr 1%nat 128 PF AGF PFS usp lo 0x8cdf8
            ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
            ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                              repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia])
            ltac:(fun Hx => exact (proj1 Hx)) ltac:(fun fl FLN => idtac).
          refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
          Time walk_to AF MST [(usp - 96, usp)] (@nil Z).
          try (lazymatch goal with ST' : stk asegs _ lo (usp + -96) |- _ => release_frame FR ST' usp end).
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
    walk_to AF MST [(usp - 112, usp)] [e_stack_malloc 1%nat; e_pixDeserialize; e_pixDestroy; e_kernelCreateFromPix; e_kernelDestroy; 0x8cdf0].
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
      walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_stack_malloc 1%nat; e_pixDeserialize; e_pixDestroy; e_kernelCreateFromPix; e_kernelDestroy; 0x8cdf0].
      frame_release_raw RT AF GP MST Σ fr 1%nat 128 PF AGF PFS usp lo 0x8cdf8
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
      walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16); (848288, 848296)]
                   [e_stack_malloc 1%nat; e_pixDeserialize; e_pixDestroy; e_kernelCreateFromPix; e_kernelDestroy; 0x8cdf0].
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
        - unfold RASTER_COST. lres_tac.
        - repeat match goal with H : rt_live RT _ = _ |- _ => rewrite H end; lia. }
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
        walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_stack_malloc 1%nat; e_pixDeserialize; e_pixDestroy; e_kernelCreateFromPix; e_kernelDestroy; 0x8cdf0].
        frame_release_g RT AF GP MST Σ fr 1%nat 128 PF AGF PFS usp lo 0x8cdf8
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
        lazymatch type of LVE with live_destroy _ _ _ (rt_live RT ?S) = rt_live RT ?S0 => rename S into S1; rename S0 into S0f end.
        lazymatch goal with H : rt_live RT S0f = rt_live RT Σ |- _ => rename H into LV0f end.
        unfold hid in POBJ.
        pose proof POBJ as (_ & _ & (HD1 & HW1 & HH1 & HWPL & HRS) & _).
        assert (WH8 : p_d v = 8 -> p_w v * p_h v <= 0x4000000)
          by (intros D8; rewrite D8 in HWPL; clear - HWPL HRS HW1 HH1; Z.div_mod_to_equations; nia).
        hide POBJ.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
        (* [comment removed for export] *)
        Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_stack_malloc 1%nat; e_pixDeserialize; e_pixDestroy; e_kernelCreateFromPix; e_kernelDestroy; 0x8cdf0].
        assert (ND1 : List.NoDup (map fst (rt_live RT S1)))
          by (lazymatch goal with A : ART RT S1 ?mm |- _ => exact (live_nodup RT AF S1 mm A LVP1) end).
        unfold hid in POBJ.
        assert (SECP : sec_bytes (rt_live RT S1) <= sec_bytes (rt_live RT Σ) + 0x4000000)
          by (pose proof (pix_destroy_sec (rt_live RT S1) _ pix v cv ND1 POBJ VDATA) as X; rewrite LVE, LV0f in X; exact X).
        hide POBJ.
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
        pose proof KFP as KF. unfold kernelCreateFromPix_cps in KF.
        eapply cps_seq.
        { eapply KF with (lo := lo) (pix := pix) (v := v) (cv := cv); rt_side idtac.
          all: lazymatch goal with
               | |- pix_obj _ _ _ _ _ => exact POBJ1
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- lres _ _ _ _ _ =>
                   unfold lres, RASTER_COST, FRAMES_MAX, LIVE_MAX in *; rewrite FRSh, FR0; cbn [length];
                   rewrite LV0f in LEN1;
                   repeat match goal with H : rt_credit RT _ = _ |- _ => rewrite H in * end;
                   split; [lia| split; [lia| split; [lia| exact LVP1]]]
               | |- p_d _ = 8 -> _ => intros D8; pose proof (WH8 D8); lia
               | |- ?g => idtac "LEFT-KFP:" g
               end. }
        Time after_call RT AF.
        fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [exact SUB01| solve [frames_sub_tac]| lia]| exact I]).
        lazymatch goal with H : ?k = 0 -> rt_live RT ?S = rt_live RT S1 |- _ => rename S into S2; rename H into LVZ2; set (kel := k) in * end.
        lazymatch goal with H : pix_obj (rt_live RT S2) _ pix v cv |- _ => rename H into POBJ2 end.
        lazymatch goal with H : kel = 0 \/ _ |- _ => rename H into KOR end.
        lazymatch goal with H : rt_frames RT S2 = rt_frames RT S1 |- _ => rename H into FRS2 end.
        lazymatch goal with H : rt_sp0 RT S2 = rt_sp0 RT S1 |- _ => rename H into SP2 end.
        lazymatch goal with H : rt_credit RT S1 - 2 ^ 30 <= rt_credit RT S2 |- _ => rename H into CR2 end.
        lazymatch goal with |- cps _ (ASTA RT S2 _ (eq (MS _ _ _ _ _ ?mm _))) _ => rename mm into m4 end.
        lazymatch goal with A : ART RT S2 m4 |- _ => rename A into ART2 end.
        assert (FRS2' : rt_frames RT S2 = (fr, 1%nat) :: rt_frames RT Σ) by (rewrite FRS2; exact FRSh).
        assert (LVP2 : forall p n, In (p, n) (rt_live RT S2) -> 0 < n).
        { destruct KOR as [KZ|(data & rows & D8 & KOBJ & LV2)]; [rewrite (LVZ2 KZ); exact LVP1|].
          rewrite LV2. intros p n Hin. apply km_live_inv in Hin as [Hin|Hin]; [| exact (LVP1 p n Hin)].
          unfold km_chunks in Hin. destruct KOBJ as (_ & _ & _ & _ & _ & _ & _ & SYB & SXB).
          destruct Hin as [E|[E|Hin]]; [injection E as <- <-; lia| injection E as <- <-; lia|].
          apply in_map_iff in Hin as (r & E & _). injection E as <- <-. lia. }
        pose proof DESTROY as DY. unfold pixDestroy_cps in DY.
        destruct KOR as [KZ|(data & rows & D8 & KOBJ & LV2)].
        -- (* [comment removed for export] *)
          pose proof (LVZ2 KZ) as LV2. clear LVZ2.
          hide POBJ2.
          refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
          (* [comment removed for export] *)
          Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_stack_malloc 1%nat; e_pixDeserialize; e_pixDestroy; e_kernelCreateFromPix; e_kernelDestroy; 0x8cdf0].
          unfold hid in POBJ2.
          lazymatch goal with A : ART RT ?S ?m0, MUx : munch _ ?m0 ?m1 |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
            assert (KL3 : keeps_live (rt_live RT S) m0 m1)
              by (apply (keeps_live_walk1 RT AF S m0 m1 fr usp (usp + -112) A ltac:(rewrite FRS2'; left; reflexivity)
                           ltac:(repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; unfold STACK_WIN; lia) MUx));
            pose proof (pix_obj_keep _ m0 m1 pix v cv KL3 POBJ2) as POBJ3; clear KL3 end.
          clear POBJ2.
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
                     [ right; exists fr, 1%nat; rewrite FRS2'; change (fs_size 1) with 128;
                       split; [left; reflexivity|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
                       split; [lia|]; split; [lia|];
                       replace (shad (fr + 32)) with (fr / 8 + 2147450884) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
                       destruct SHC4 as [[_ B] _]; exact B
                     | unfold SEGTOP_A; repeat split; first [lia | clear - FR64; Z.div_mod_to_equations; lia] ]
                 | |- rw_cells _ _ _ [C8 _] => exact FRMp
                 | |- pix_obj _ _ _ _ _ => exact POBJ3
                 | |- uctx _ _ _ _ =>
                     unfold uctx; rewrite !unsigned_lit by lia; unfold parked in S0INV;
                     apply chain_ok_push with (fp1 := bv_unsigned s0);
                       [ lia | clear - SPA; Z.div_mod_to_equations; lia | unfold USTACK_TOP; lia | unfold RA_TOP; lia | apply bv_unsigned_in_range
                       | rewrite Z_to_bv_bv_unsigned; rewrite <- RATOP; rewrite Z_to_bv_bv_unsigned;
                         lazymatch type of FRrec17 with rw_cells _ _ ?a _ => replace (usp + -16) with a by lia end; exact FRrec17
                       | cbn [chain_ok]; unfold link_invalid; lia ]
                 | |- Forall _ _ => exact tr_destroy
                 | |- lenv _ _ _ _ _ _ => lenv_tac
                 | |- lres _ _ _ _ _ =>
                     unfold lres, RASTER_COST, FRAMES_MAX, LIVE_MAX in *; rewrite FRS2', FR0; cbn [length]; rewrite LV2;
                     split; [lia| split; [rewrite LV0f in LEN1; lia| split; [repeat match goal with H : rt_credit RT _ = _ |- _ => rewrite H in * end; lia| exact LVP1]]]
                 | |- ?g => idtac "LEFT-DY:" g
                 end. }
          clear SHC4.
          Time after_call RT AF.
          lazymatch goal with H : rt_live RT ?S = live_destroy pix v cv (rt_live RT S2) |- _ => rename S into S3; rename H into LV3r end.
          lazymatch goal with |- cps _ (ASTA RT S3 _ (eq (MS _ _ _ _ _ ?mm _))) _ => rename mm into m5 end.
          assert (LV3 : rt_live RT S3 = rt_live RT Σ) by (rewrite LV3r, LV2, LVE, LV0f; reflexivity).
          clear POBJ3.
          fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; rewrite LV3; exact He| solve [frames_sub_tac]| lia]|
                                          cbn [outside]; destruct (NFA _ Hx) as [N1 N2]; split; [lia| exact I]]).
          lazymatch goal with H : rt_frames RT S3 = rt_frames RT S2 |- _ => assert (FRS3 : rt_frames RT S3 = (fr, 1%nat) :: rt_frames RT Σ) by (rewrite H; exact FRS2') end.
          assert (LVP3 : forall p n, In (p, n) (rt_live RT S3) -> 0 < n) by (rewrite LV3; exact LVP).
          refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
          (* [comment removed for export] *)
          Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_stack_malloc 1%nat; e_pixDeserialize; e_pixDestroy; e_kernelCreateFromPix; e_kernelDestroy; 0x8cdf0].
          split_at FRMq 1%nat FRMk. split_at FRMk 1%nat FRMl.
          pose proof FSH as SHC. split_at SHC 8%nat SHC8. split_at SHC8 1%nat SHC9. clear SHC SHC9.
          at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                        ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                              repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
          pose proof KD as KDc. unfold kernelDestroy_cps in KDc.
          eapply cps_seq.
          { eapply KDc with (lo := lo) (pp := fr + 64) (kel := kel) (sy := 0) (sx := 0) (cy := 0) (cx := 0) (data := 0) (rows := []); rt_side idtac.
            all: lazymatch goal with
                 | |- optrF _ _ _ _ _ =>
                     unfold optrF, parked in *; split;
                     [ exists fr, 1%nat; rewrite FRS3; change (fs_size 1) with 128;
                       split; [left; reflexivity|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
                       split; [lia|]; split; [lia|];
                       replace (shad (fr + 64)) with (fr / 8 + 2147450888) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
                       destruct SHC8 as [[_ B] _]; exact B
                     | unfold SEGTOP_A; repeat split; first [lia | clear - FR64; Z.div_mod_to_equations; lia] ]
                 | |- rw_cells _ _ _ [C8 _] => exact FRMk
                 | |- _ = 0 \/ _ => left; exact KZ
                 | |- lenv _ _ _ _ _ _ => lenv_tac
                 | |- lres _ _ _ _ _ =>
                     unfold lres, RASTER_COST, FRAMES_MAX, LIVE_MAX in *; rewrite FRS3, FR0, LV3; cbn [length];
                     split; [lia| split; [lia| split; [repeat match goal with H : rt_credit RT _ = _ |- _ => rewrite H in * end; lia| exact LVP]]]
                 | |- ?g => idtac "LEFT-KD:" g
                 end. }
          clear SHC8.
          Time after_call RT AF.
          lazymatch goal with H : rt_live RT ?S = (if kel =? 0 then rt_live RT S3 else _) |- _ => rename S into S4; rename H into LV4r end.
          assert (LV4 : rt_live RT S4 = rt_live RT Σ) by (rewrite LV4r, KZ; cbn; exact LV3).
          fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; rewrite LV4; exact He| solve [frames_sub_tac]| lia]|
                                          cbn [outside]; destruct (NFA _ Hx) as [N1 N2]; split; [lia| exact I]]).
          clear LV4r LV3r PIN IN.
          (* [comment removed for export] *)
          repeat match goal with H : rw_cells asegs _ (usp + -16) _ |- _ => clear H end.
          repeat match goal with H : rw_cells asegs _ (fr + _) _ |- _ => clear H end.
          repeat match goal with H : ART RT _ ?mm |- cps _ (ASTA RT _ _ (eq (MS _ _ _ _ _ ?mc _))) _ => lazymatch mm with mc => fail | m => fail | _ => clear H end end.
          refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
          (* [comment removed for export] *)
          Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_stack_malloc 1%nat; e_pixDeserialize; e_pixDestroy; e_kernelCreateFromPix; e_kernelDestroy; 0x8cdf0].
          Time frame_release_g RT AF GP MST Σ fr 1%nat 128 PF AGF PFS usp lo 0x8cdf8
            ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
            ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                              repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia])
            ltac:(fun Hx => exact (proj1 Hx)) ltac:(fun fl FLN => idtac).
          refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
          Time walk_to AF MST [(usp - 112, usp)] (@nil Z).
          try (lazymatch goal with ST' : stk asegs _ lo (usp + -112) |- _ => release_frame FR ST' usp end).
          cps_stop.
          apply cps_finish; intros c Hc; subst QF; cbv beta.
          lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S end.
          split; [| unfold RASTER_COST in *; alg_tac].
          eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-; eexists.
          split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
          split; [split; [assumption| split; assumption]|].
          split; [intros a Ha Ho; exact (AGF a (conj Ha Ho))|].
          lazymatch goal with LHx : LIBH ?mm |- LIB ?mm => destruct LHx as (LH0 & LHH); split; [exact LH0| eexists; exact LHH] end.
        -- (* [comment removed for export] *)
          assert (ND2 : List.NoDup (map fst (km_live kel data (p_h v) (p_w v) rows (rt_live RT S1))))
            by (lazymatch goal with A : ART RT S2 ?mm |- _ => pose proof (live_nodup RT AF S2 mm A LVP2) as ND; rewrite LV2 in ND; exact ND end).
          hide POBJ2. hide KOBJ.
          refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
          (* [comment removed for export] *)
          Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_stack_malloc 1%nat; e_pixDeserialize; e_pixDestroy; e_kernelCreateFromPix; e_kernelDestroy; 0x8cdf0].
          unfold hid in POBJ2, KOBJ.
          lazymatch goal with A : ART RT ?S ?m0, MUx : munch _ ?m0 ?m1 |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
            assert (KL3 : keeps_live (rt_live RT S) m0 m1)
              by (apply (keeps_live_walk1 RT AF S m0 m1 fr usp (usp + -112) A ltac:(rewrite FRS2'; left; reflexivity)
                           ltac:(repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; unfold STACK_WIN; lia) MUx));
            pose proof (pix_obj_keep _ m0 m1 pix v cv KL3 POBJ2) as POBJ3;
            pose proof (kel_obj_keep _ m0 m1 kel (p_h v) (p_w v) 2 2 data rows KL3 KOBJ) as KOBJ3; clear KL3 end.
          clear POBJ2 KOBJ.
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
                     [ right; exists fr, 1%nat; rewrite FRS2'; change (fs_size 1) with 128;
                       split; [left; reflexivity|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
                       split; [lia|]; split; [lia|];
                       replace (shad (fr + 32)) with (fr / 8 + 2147450884) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
                       destruct SHC4 as [[_ B] _]; exact B
                     | unfold SEGTOP_A; repeat split; first [lia | clear - FR64; Z.div_mod_to_equations; lia] ]
                 | |- rw_cells _ _ _ [C8 _] => exact FRMp
                 | |- pix_obj _ _ _ _ _ => exact POBJ3
                 | |- uctx _ _ _ _ =>
                     unfold uctx; rewrite !unsigned_lit by lia; unfold parked in S0INV;
                     apply chain_ok_push with (fp1 := bv_unsigned s0);
                       [ lia | clear - SPA; Z.div_mod_to_equations; lia | unfold USTACK_TOP; lia | unfold RA_TOP; lia | apply bv_unsigned_in_range
                       | rewrite Z_to_bv_bv_unsigned; rewrite <- RATOP; rewrite Z_to_bv_bv_unsigned;
                         lazymatch type of FRrec17 with rw_cells _ _ ?a _ => replace (usp + -16) with a by lia end; exact FRrec17
                       | cbn [chain_ok]; unfold link_invalid; lia ]
                 | |- Forall _ _ => exact tr_destroy
                 | |- lenv _ _ _ _ _ _ => lenv_tac
                 | |- lres _ _ _ _ _ =>
                     unfold lres, RASTER_COST, FRAMES_MAX, LIVE_MAX in *; rewrite FRS2', FR0; cbn [length];
                     split; [lia| split; [rewrite LV2, km_live_length; destruct KOBJ3 as (_ & _ & _ & _ & KLEN & _); rewrite KLEN; rewrite LV0f in LEN1; lia|
                     split; [repeat match goal with H : rt_credit RT _ = _ |- _ => rewrite H in * end; lia| exact LVP2]]]
                 | |- ?g => idtac "LEFT-DY:" g
                 end. }
          clear SHC4.
          Time after_call RT AF.
          lazymatch goal with H : rt_live RT ?S = live_destroy pix v cv (rt_live RT S2) |- _ => rename S into S3; rename H into LV3r end.
          lazymatch goal with |- cps _ (ASTA RT S3 _ (eq (MS _ _ _ _ _ ?mm _))) _ => rename mm into m5 end.
          assert (LV3 : rt_live RT S3 = km_live kel data (p_h v) (p_w v) rows (rt_live RT Σ))
            by (rewrite LV3r, LV2, (live_destroy_km kel data (p_h v) (p_w v) rows (rt_live RT S1) _ pix v cv ND2 POBJ1), LVE, LV0f; reflexivity).
          lazymatch goal with AGx : agree_on (fun a => aclient (rt_live RT S3) _ _ a /\ outside [(fr + 32, fr + 32 + 8)] a) ?ma ?mb, A3 : ART RT S3 ?mb |- _ =>
            assert (KL5 : keeps_live (rt_live RT S3) ma mb)
              by (eapply keeps_live_of_agree; [exact AGx| intros e He; exact He|];
                  intros qq kk xx Hq Hx; cbn [outside]; split; [| exact I];
                  let FLV := fresh "FLV" in
                  pose proof (af_frames_range RT AF S3 mb fr 1%nat A3
                                ltac:(repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; left; reflexivity)) as (_ & _ & _ & FLV);
                  specialize (FLV qq kk Hq); change (fs_size 1) with 128 in FLV; lia);
            assert (KOBJ4 : kel_obj (rt_live RT S3) mb kel (p_h v) (p_w v) 2 2 data rows)
              by (apply (kel_obj_keep _ ma mb kel (p_h v) (p_w v) 2 2 data rows KL5);
                  apply (kel_obj_move (rt_live RT S2)); [| exact KOBJ3];
                  intros e He; rewrite LV3; destruct He as [<-|[<-|He]];
                  [ apply km_live_in_kel | apply km_live_in_data | apply in_map_iff in He as (r & <- & Hr); apply km_live_in_row; exact Hr ]);
            clear KL5 end.
          clear POBJ3 KOBJ3.
          fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; rewrite LV3; apply km_live_in_old; exact He| solve [frames_sub_tac]| lia]|
                                          cbn [outside]; destruct (NFA _ Hx) as [N1 N2]; split; [lia| exact I]]).
          lazymatch goal with H : rt_frames RT S3 = rt_frames RT S2 |- _ => assert (FRS3 : rt_frames RT S3 = (fr, 1%nat) :: rt_frames RT Σ) by (rewrite H; exact FRS2') end.
          assert (LVP3 : forall p n, In (p, n) (rt_live RT S3) -> 0 < n)
            by (intros p n Hin; rewrite LV3r in Hin; apply live_destroy_sub in Hin; exact (LVP2 p n Hin)).
          hide KOBJ4.
          refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
          (* [comment removed for export] *)
          Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_stack_malloc 1%nat; e_pixDeserialize; e_pixDestroy; e_kernelCreateFromPix; e_kernelDestroy; 0x8cdf0].
          unfold hid in KOBJ4.
          try (lazymatch goal with A : ART RT ?S ?m0, MUx : munch _ ?m0 ?m1 |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
            assert (KL6 : keeps_live (rt_live RT S) m0 m1)
              by (apply (keeps_live_walk1 RT AF S m0 m1 fr usp (usp + -112) A ltac:(rewrite FRS3; left; reflexivity)
                           ltac:(repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; unfold STACK_WIN; lia) MUx));
            pose proof (kel_obj_keep _ m0 m1 kel (p_h v) (p_w v) 2 2 data rows KL6 KOBJ4) as KOBJ5; clear KL6 KOBJ4 end).
          try (rename KOBJ4 into KOBJ5).
          split_at FRMq 1%nat FRMk. split_at FRMk 1%nat FRMl.
          pose proof FSH as SHC. split_at SHC 8%nat SHC8. split_at SHC8 1%nat SHC9. clear SHC SHC9.
          at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                        ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                              repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
          pose proof KD as KDc. unfold kernelDestroy_cps in KDc.
          eapply cps_seq.
          { eapply KDc with (lo := lo) (pp := fr + 64) (kel := kel) (sy := p_h v) (sx := p_w v) (cy := 2) (cx := 2) (data := data) (rows := rows); rt_side idtac.
            all: lazymatch goal with
                 | |- optrF _ _ _ _ _ =>
                     unfold optrF, parked in *; split;
                     [ exists fr, 1%nat; rewrite FRS3; change (fs_size 1) with 128;
                       split; [left; reflexivity|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
                       split; [lia|]; split; [lia|];
                       replace (shad (fr + 64)) with (fr / 8 + 2147450888) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
                       destruct SHC8 as [[_ B] _]; exact B
                     | unfold SEGTOP_A; repeat split; first [lia | clear - FR64; Z.div_mod_to_equations; lia] ]
                 | |- rw_cells _ _ _ [C8 _] => exact FRMk
                 | |- _ = 0 \/ _ => right; exact KOBJ5
                 | |- lenv _ _ _ _ _ _ => lenv_tac
                 | |- lres _ _ _ _ _ =>
                     unfold lres, RASTER_COST, FRAMES_MAX, LIVE_MAX in *; rewrite FRS3, FR0; cbn [length];
                     split; [lia| split; [rewrite LV3, km_live_length; destruct KOBJ5 as (_ & _ & _ & _ & KLEN & _); rewrite KLEN; lia|
                     split; [repeat match goal with H : rt_credit RT _ = _ |- _ => rewrite H in * end; lia| exact LVP3]]]
                 | |- ?g => idtac "LEFT-KD:" g
                 end. }
          assert (KNZ : kel <> 0) by (destruct KOBJ5 as (_ & (_ & K0 & _) & _); lia).
          lazymatch goal with A : ART RT S3 ?mm |- _ =>
            pose proof (live_nodup RT AF S3 mm A LVP3) as KND0; rewrite LV3 in KND0;
            destruct (km_live_nodup_split kel data (p_h v) (p_w v) rows (rt_live RT Σ) KND0) as [KND NIN]; clear KND0 end.
          clear SHC8 KOBJ5.
          Time after_call RT AF.
          lazymatch goal with H : rt_live RT ?S = (if kel =? 0 then rt_live RT S3 else _) |- _ => rename S into S4; rename H into LV4r end.
          assert (LV4 : rt_live RT S4 = rt_live RT Σ)
            by (rewrite LV4r; replace (kel =? 0) with false by (symmetry; apply Z.eqb_neq; exact KNZ); rewrite LV3;
                exact (km_unlive_live kel data (p_h v) (p_w v) rows (rt_live RT Σ) KND NIN)).
          fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; rewrite LV4; exact He| solve [frames_sub_tac]| lia]|
                                          cbn [outside]; destruct (NFA _ Hx) as [N1 N2]; split; [lia| exact I]]).
          clear LV4r LV3r PIN IN KND NIN ND2.
          (* [comment removed for export] *)
          repeat match goal with H : rw_cells asegs _ (usp + -16) _ |- _ => clear H end.
          repeat match goal with H : rw_cells asegs _ (fr + _) _ |- _ => clear H end.
          repeat match goal with H : ART RT _ ?mm |- cps _ (ASTA RT _ _ (eq (MS _ _ _ _ _ ?mc _))) _ => lazymatch mm with mc => fail | m => fail | _ => clear H end end.
          refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
          (* [comment removed for export] *)
          Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_stack_malloc 1%nat; e_pixDeserialize; e_pixDestroy; e_kernelCreateFromPix; e_kernelDestroy; 0x8cdf0].
          Time frame_release_g RT AF GP MST Σ fr 1%nat 128 PF AGF PFS usp lo 0x8cdf8
            ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
            ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                              repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia])
            ltac:(fun Hx => exact (proj1 Hx)) ltac:(fun fl FLN => idtac).
          refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
          Time walk_to AF MST [(usp - 112, usp)] (@nil Z).
          try (lazymatch goal with ST' : stk asegs _ lo (usp + -112) |- _ => release_frame FR ST' usp end).
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
End KMFUZZ.
