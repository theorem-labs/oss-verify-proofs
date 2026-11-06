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
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.B08 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit Lept_chain Lept_leaf LeptC_leaf Lept_objkit Cf_iface Cf_kit CfF_kit LeptB_guard.
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
Lemma tr_cfcreate : Forall (fun f => In [f; RA_CF_CREATE; RA_TOP] CLIENT_TRACES) [0x8ee4c; 0x8e74c; 0x93e80].
Proof. apply Forall_forall. intros f Hf. cbn [In] in Hf. destruct Hf as [<-|[<-|[<-|[]]]]; vm_compute; tauto. Qed.

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
      assert (E1 := rw_cells_agree_nw asegs mm m' _ _ D1 (static_agree RT GP client_static mm m' AGS (fun a Ha => Ha) 0xd0de0 4 ltac:(cbn; tauto)));
      assert (E2 := rw_cells_agree_nw asegs mm m' _ _ D2 (static_agree RT GP client_static mm m' AGS (fun a Ha => Ha) 0xd0e20 8 ltac:(cbn; tauto)));
      assert (E3 := rw_cells_agree_nw asegs mm m' _ _ D3 (static_agree RT GP client_static mm m' AGS (fun a Ha => Ha) 0xd0e40 8 ltac:(cbn; tauto)));
      assert (E4 := rw_cells_agree_nw asegs mm m' _ _ D4 (static_agree RT GP client_static mm m' AGS (fun a Ha => Ha) 0xd0e00 8 ltac:(cbn; tauto)));
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

Section CFFUZZ.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis DESER : pixDeserialize_cps RT.
Hypothesis DESTROY : pixDestroy_cps RT.
Hypothesis CFC : l_colorfillCreate_cps RT.
Hypothesis CFD : l_colorfillDestroy_cps RT.

Theorem cf_fuzz_ok : cf_fuzz_one_cps RT.
Proof using AF RC GP DESER DESTROY CFC CFD.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d bs lo
    FDO MST -> -> -> RATOP DPOS BSL BYTES OWN FR0 LVP LVB CRB S0INV LIBm SSP ART0 MI ST LOW LOR SPT SPA SPB.
  destruct LIBm as ((LSEV & LALLOC & LDEALLOC) & (h0 & LHAND)).
  unfold g_LeptMsgSeverity, g_pix_alloc, g_pix_dealloc, g_stderr_handler in *. clear BYTES.
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, e_cf_fuzz, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold FUZZ_STACK, FUZZ_COST, CF_FUZZ_LIVE, LSTK, STDERR_STACK, RASTER_COST in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
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
    walk_to AF MST [(usp - 96, usp)] [e_stack_malloc 1%nat; e_pixDeserialize; e_pixDestroy; e_colorfillCreate; e_colorfillDestroy].
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
      walk_to AF MST [(usp - 96, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_stack_malloc 1%nat; e_pixDeserialize; e_pixDestroy; e_colorfillCreate; e_colorfillDestroy; 0x8d778].
      frame_release_raw RT AF GP MST Σ fr 1%nat 128 PF AGF PFS usp lo 0x8d780
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
      walk_to AF MST [(usp - 96, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16); (855552, 855560)]
                   [e_stack_malloc 1%nat; e_pixDeserialize; e_pixDestroy; e_colorfillCreate; e_colorfillDestroy; 0x8d778].
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
        walk_to AF MST [(usp - 96, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_stack_malloc 1%nat; e_pixDeserialize; e_pixDestroy; e_colorfillCreate; e_colorfillDestroy; 0x8d778].
        frame_release_g RT AF GP MST Σ fr 1%nat 128 PF AGF PFS usp lo 0x8d780
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
        pose proof POBJ as (PXC & (PIN & PX0 & PX16 & _) & _).
        chunk_facts RT AF GP pix 64.
        lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ =>
          assert (NCP : forall a, PF a -> a < pix \/ pix + 64 <= a)
            by (intros a [Ha _]; apply (inner_chunk_apart RT AF S mm pix 64 (rt_live RT Σ) (rt_frames RT Σ) usp a A PIN);
                [ intros e He; apply (live_destroy_in pix v cv); rewrite LVE;
                  repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact He
                | intros e He; rewrite FR0 in He; destruct He
                | repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul
                | exact Ha ]) end.
        lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ =>
          assert (FRSh : rt_frames RT S = (fr, 1%nat) :: rt_frames RT Σ)
            by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity) end.
        fframe_chunk RT AF fr 1%nat 128 pix 64. norm_fshadow.
        unfold pix_cells in PXC. hide POBJ.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
        walk_to AF MST [(usp - 96, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)]
                     [e_stack_malloc 1%nat; e_pixDeserialize; e_pixDestroy; e_colorfillCreate; e_colorfillDestroy; 0x8d778].
        unfold hid in POBJ.
        lazymatch goal with A : ART RT ?S ?m0, MUx : munch _ ?m0 ?m1 |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
          assert (KL1 : keeps_live (rt_live RT S) m0 m1)
            by (apply (keeps_live_walk1 RT AF S m0 m1 fr usp (usp + -96) A ltac:(rewrite FRSh; left; reflexivity)
                         ltac:(repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; unfold STACK_WIN; lia) MUx));
          pose proof (pix_obj_keep _ m0 m1 pix v cv KL1 POBJ) as POBJ'; clear KL1 end.
        clear POBJ.
        pose proof FR as FRrec. split_before FRrec (C8 s0) FRrec3. clear FRrec.
        at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                            repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
        pose proof CFC as CC. unfold l_colorfillCreate_cps in CC.
        eapply cps_seq.
        { eapply CC with (lo := lo) (pix := pix) (v := v) (cv := cv) (ras := [RA_TOP]); rt_side idtac.
          - unfold uctx. rewrite !unsigned_lit by lia. unfold parked in S0INV.
            apply chain_ok_push with (fp1 := bv_unsigned s0);
              [ lia | clear - SPA; Z.div_mod_to_equations; lia | unfold USTACK_TOP; lia | unfold RA_TOP; lia | apply bv_unsigned_in_range | | cbn [chain_ok]; unfold link_invalid; lia ].
            rewrite Z_to_bv_bv_unsigned. rewrite <- RATOP. rewrite Z_to_bv_bv_unsigned.
            lazymatch type of FRrec3 with rw_cells _ _ ?a _ => replace (usp + -16) with a by lia end. exact FRrec3.
          - exact tr_cfcreate.
          - lenv_tac.
          - unfold lres, RASTER_COST, FRAMES_MAX, LIVE_MAX in *. rewrite FRSh, FR0. cbn [length].
            lazymatch goal with LB : Z.of_nat (length (rt_live RT ?S)) <= Z.of_nat (length (rt_live RT ?S0)) + 4, LP : forall p n, In (p, n) (rt_live RT ?S) -> 0 < n |- _ =>
              repeat match goal with H : rt_live RT S0 = _ |- _ => rewrite H in LB end;
              repeat match goal with H : rt_credit RT _ = _ |- _ => rewrite H in * end;
              split; [lia| split; [lia| split; [lia| exact LP]]] end. }
        after_call RT AF.
        lazymatch goal with H : ?c = 0 -> rw_cells _ _ pix _ |- _ => rename H into CF0; set (cf := c) in * end.
        lazymatch goal with H : cf <> 0 -> _ |- _ => rename H into CFN end.
        lazymatch goal with H : rt_live RT _ = (if cf =? 0 then _ else _) |- _ => rename H into LV2 end.
        lazymatch type of CFN with _ -> cf_obj _ _ _ ?c /\ _ => set (cfc := c) in * end.
        match goal with H : rt_credit RT _ - 2 <= rt_credit RT _ |- _ => rename H into CR2 end.
        (* [comment removed for export] *)
        lazymatch goal with AGx : agree_on _ ?ma ?mb, A : ART RT ?S ?ma |- cps _ (ASTA RT _ _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
          assert (KC2 : keeps_cmap v ma mb)
            by (apply (keeps_cmap_of_agree _ _ _ _ _ v cv _ ma mb pix POBJ' AGx (fun e He => He)); intros NZ CIN zx Hzx;
                assert (NE1 : p_cmap v <> pix) by (destruct POBJ' as (_ & _ & _ & _ & [CZ0|(_ & NE1 & _)]); [contradiction| exact NE1]);
                pose proof (live_apart RT AF S ma (p_cmap v) 24 pix 64 A CIN PIN NE1) as D; cbn [outside]; split; [clear - D Hzx; lia| exact I]) end.
        fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx));
                                          [ intros e He; apply (fun l H => proj1 (live_destroy_in pix v cv l e H)); rewrite LVE;
                                            repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact He
                                          | solve [frames_sub_tac] | lia]
                                       | cbn [outside]; pose proof (NCP _ Hx) as HxN; split; [clear - HxN; lia| exact I]]).
        (* [comment removed for export] *)
        lazymatch goal with A : ART RT ?S2 ?mm |- cps _ (ASTA RT ?S2 _ _) _ =>
          lazymatch type of PIN with In _ (rt_live RT ?S1) =>
            assert (SUB12 : forall e, In e (rt_live RT S1) -> In e (rt_live RT S2))
              by (intros e He; rewrite LV2; destruct (Z.eqb_spec cf 0) as [CZ|CNZ]; [exact He| rewrite cf_live_app; apply in_or_app; right; exact He]);
            assert (LVP2 : forall p n, In (p, n) (rt_live RT S2) -> 0 < n)
              by (intros p n Hin; rewrite LV2 in Hin; destruct (Z.eqb_spec cf 0) as [CZ|CNZ]; [exact (LVP1 p n Hin)|];
                  rewrite cf_live_app in Hin; apply in_app_or in Hin; destruct Hin as [Hin|Hin]; [| exact (LVP1 p n Hin)];
                  cbn [cf_live In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; clear; lia|]); destruct Hin);
            assert (LEN2 : Z.of_nat (length (rt_live RT S2)) <= Z.of_nat (length (rt_live RT S1)) + 12)
              by (rewrite LV2; destruct (Z.eqb_spec cf 0) as [CZ|CNZ]; [clear; lia| cbn [cf_live length]; clear; lia]);
            assert (FRS2 : rt_frames RT S2 = (fr, 1%nat) :: rt_frames RT Σ)
              by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity)
          end end.
        pose proof (SUB12 _ PIN) as PIN2.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
        walk_to AF MST [(usp - 96, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)]
                     [e_stack_malloc 1%nat; e_pixDeserialize; e_pixDestroy; e_colorfillCreate; e_colorfillDestroy; 0x8d778].
        lazymatch goal with A : ART RT ?S ?m0, MUx : munch _ ?m0 ?m1 |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
          assert (KL3 : keeps_live (rt_live RT S) m0 m1)
            by (apply (keeps_live_walk1 RT AF S m0 m1 fr usp (usp + -96) A ltac:(rewrite FRS2; left; reflexivity)
                         ltac:(repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; unfold STACK_WIN; lia) MUx));
          assert (KC3 : keeps_cmap v m0 m1) by (exact (keeps_cmap_of_live _ _ v cv _ m0 m1 pix POBJ' SUB12 KL3));
          (* [comment removed for export] *)
          assert (PRE : cf = 0 \/ (cf_obj (rt_live RT S) m1 cf cfc /\ cf_pix cfc = pix /\ pix_obj_rc (rt_live RT S) m1 pix v cv 2
                                   /\ ~ In pix (map fst (cf_live cf cfc []))))
            by (destruct (Z.eq_dec cf 0) as [CZ|CNZ]; [left; exact CZ| right];
                destruct (CFN CNZ) as (CFO & CFP & PXC2);
                split; [exact (cf_obj_keep_all _ m0 m1 cf cfc CFO KL3)|]; split; [exact CFP|]; split;
                [ apply (pix_obj_rc_rebuild _ _ _ m1 pix v cv 2 POBJ' SUB12);
                  [ exact (keeps_live_cells _ m0 m1 pix 64 pix (pix_cells_rc v 2) KL3 PIN2 ltac:(clear; lia) ltac:(cbn; clear; lia) PXC2)
                  | exact (keeps_cmap_trans v _ _ _ KC2 KC3) ]
                | pose proof (live_nodup RT AF S m0 A LVP2) as ND; rewrite LV2 in ND;
                  replace (cf =? 0) with false in ND by (symmetry; apply Z.eqb_neq; exact CNZ);
                  rewrite cf_live_app, map_app in ND;
                  exact (nodup_app_notin _ _ pix ND (in_map fst _ _ PIN)) ]);
          (* [comment removed for export] *)
          assert (PXCZ : cf = 0 -> rw_cells asegs m1 pix (pix_cells_rc v 1))
            by (intros CZ; exact (keeps_live_cells _ m0 m1 pix 64 pix (pix_cells_rc v 1) KL3 PIN2 ltac:(clear; lia) ltac:(cbn; clear; lia) (CF0 CZ)))
        end.
        (* [comment removed for export] *)
        split_at FRM 4%nat PPC2. split_at PPC2 1%nat FRMb. split_at FRMb 1%nat PPCF. split_at PPCF 1%nat FRMc.
        pose proof FSH as SHC. split_at SHC 8%nat SHC8. split_at SHC8 1%nat SHC9. clear SHC SHC9.
        at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                            repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
        pose proof CFD as CD. unfold l_colorfillDestroy_cps in CD.
        eapply cps_seq.
        { eapply CD with (lo := lo) (pp := fr + 64) (cf := cf) (pix := pix) (c := cfc) (v := v) (cv := cv); rt_side idtac.
          all: lazymatch goal with
               | |- optrF _ _ _ _ _ =>
                   unfold optrF, own_frame, parked in *; split;
                   [ exists fr, 1%nat; rewrite FRS2; change (fs_size 1) with 128;
                     split; [left; reflexivity|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
                     split; [lia|]; split; [lia|];
                     replace (shad (fr + 64)) with (fr / 8 + 2147450888) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
                     destruct SHC8 as [[_ B] _]; exact B
                   | unfold SEGTOP_A; repeat split; first [lia | clear - FR64; Z.div_mod_to_equations; lia] ]
               | |- rw_cells _ _ _ [C8 _] => exact PPCF
               | |- _ \/ _ => exact PRE
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- lres _ _ _ _ _ =>
                   unfold lres, RASTER_COST, FRAMES_MAX, LIVE_MAX in *; rewrite FRS2, FR0; cbn [length];
                   repeat match goal with H : rt_live RT _ = rt_live RT _ |- _ => rewrite H in * end;
                   repeat match goal with H : rt_credit RT _ = _ |- _ => rewrite H in * end;
                   split; [lia| split; [lia| split; [lia| exact LVP2]]]
               | |- ?g => idtac "LEFT-CFD:" g
               end. }
        clear SHC8.
        after_call RT AF.
        lazymatch goal with H : cf = 0 -> rt_pres_fp _ _ _ _ _ _ |- _ => rename H into KEEP0 end.
        lazymatch goal with H : cf <> 0 -> rt_pres_fp _ _ _ _ _ _ /\ _ |- _ => rename H into KEEPN end.
        lazymatch goal with H : rt_live RT _ = (if cf =? 0 then _ else cf_live_destroy _ _ _) |- _ => rename H into LV3raw end.
        match goal with H : rt_credit RT _ - 2 <= rt_credit RT _ |- _ => lazymatch H with CR2 => fail | _ => rename H into CR3 end end.
        (* [comment removed for export] *)
        lazymatch type of LVP2 with forall p n, In _ (rt_live RT ?S2) -> _ =>
          lazymatch type of PIN with In _ (rt_live RT ?S1) =>
            match goal with A : ART RT S2 ?mm |- _ =>
              assert (NDN : cf <> 0 -> List.NoDup (map fst (cf_live cf cfc []) ++ map fst (rt_live RT S1)))
                by (intros CNZ; pose proof (live_nodup RT AF S2 mm A LVP2) as ND; rewrite LV2 in ND;
                    replace (cf =? 0) with false in ND by (symmetry; apply Z.eqb_neq; exact CNZ);
                    rewrite cf_live_app, map_app in ND; exact ND) end end end.
        (* [comment removed for export] *)
        lazymatch type of KEEP0 with _ -> rt_pres_fp (rt_live RT ?S3) ?frs ?spc _ ?ma ?mb =>
          lazymatch type of PIN with In _ (rt_live RT ?S1) =>
            assert (LV3 : rt_live RT S3 = rt_live RT S1)
              by (rewrite LV3raw, LV2; destruct (Z.eqb_spec cf 0) as [CZ|CNZ]; [reflexivity|];
                  destruct (CFN CNZ) as ((_ & _ & _ & _ & _ & _ & CND) & _);
                  apply (cf_live_roundtrip cf cfc _ CND); intros e He;
                  exact (nodup_app_notin _ _ (fst e) (NDN CNZ) (in_map fst _ _ He)));
            assert (P : rt_pres_fp (rt_live RT S3) frs spc [(fr + 64, fr + 64 + 8); (pix + 20, pix + 24)] ma mb)
              by (destruct (Z.eq_dec cf 0) as [CZ|CNZ]; [intros a Ha _; exact (KEEP0 CZ a Ha I)| exact (proj1 (KEEPN CNZ))]);
            assert (PXC3 : rw_cells asegs mb pix (pix_cells v))
              by (destruct (Z.eq_dec cf 0) as [CZ|CNZ]; [| exact (proj2 (proj2 (KEEPN CNZ)))];
                  apply (rw_cells_agree_nw asegs ma mb _ _ (PXCZ CZ)); intros a Ha; apply (KEEP0 CZ); [| exact I];
                  right; right; left; exists pix, 64; split; [rewrite LV3; exact PIN| cbn in Ha; clear - Ha; lia])
          end end.
        lazymatch type of P with rt_pres_fp ?lv ?frs ?spc ?W ?ma ?mb =>
          assert (AG : agree_on (fun a => aclient lv frs spc a /\ outside W a) ma mb) by (intros ? [Ha Hb]; exact (P _ Ha Hb));
          clear P; rt_transport ma mb AG ltac:(fun A => split; [acl_dispatch A | outside_side]) end.
        lazymatch type of AG with agree_on _ ?ma ?mb =>
          lazymatch type of PIN with In _ (rt_live RT ?S1) =>
            match goal with A : ART RT S1 ?mm |- _ =>
              assert (KC4 : keeps_cmap v ma mb)
                by (apply (keeps_cmap_of_agree _ _ _ _ _ v cv _ ma mb pix POBJ' AG ltac:(intros e He; rewrite LV3; exact He)); intros NZ CIN zx Hzx;
                    assert (NE1 : p_cmap v <> pix) by (destruct POBJ' as (_ & _ & _ & _ & [CZ0|(_ & NE1 & _)]); [contradiction| exact NE1]);
                    exact (chunk_outside_local RT AF S1 mm fr 1%nat (p_cmap v) 24 (fr + 64) (fr + 64 + 8) pix zx A
                             ltac:(rewrite FRSh; left; reflexivity) ltac:(clear; lia) ltac:(change (fs_size 1) with 128; clear; lia) CIN PIN NE1 Hzx)) end end end.
        fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx));
                                          [ intros e He; rewrite LV3; apply (fun l H => proj1 (live_destroy_in pix v cv l e H)); rewrite LVE;
                                            repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact He
                                          | solve [frames_sub_tac] | lia]
                                       | cbn [outside]; pose proof (NCP _ Hx) as HxN; destruct (NFA _ Hx) as [HxF _];
                                         split; [clear - HxF; lia| split; [clear - HxN; lia| exact I]]]).
        lazymatch goal with A : ART RT ?S3 ?mb |- cps _ (ASTA RT ?S3 _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
          assert (POBJ3 : pix_obj (rt_live RT S3) mb pix v cv)
            by (apply pix_obj_rc_1; apply (pix_obj_rc_rebuild _ _ _ mb pix v cv 1 POBJ');
                [ intros e He; rewrite LV3; exact He | exact PXC3
                | exact (keeps_cmap_trans v _ _ _ KC2 (keeps_cmap_trans v _ _ _ KC3 KC4)) ]);
          assert (FRS3 : rt_frames RT S3 = (fr, 1%nat) :: rt_frames RT Σ)
            by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity);
          assert (LVP3 : forall p n, In (p, n) (rt_live RT S3) -> 0 < n) by (rewrite LV3; exact LVP1);
          assert (PIN3 : In (pix, 64) (rt_live RT S3)) by (rewrite LV3; exact PIN) end.
        clear LV3raw KEEP0 KEEPN PRE PXCZ NDN LV2 CF0 CFN SUB12 LVP2 LEN2 PIN2 KC2 KC3 KC4 POBJ'.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
        walk_to AF MST [(usp - 96, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)]
                     [e_stack_malloc 1%nat; e_pixDeserialize; e_pixDestroy; e_colorfillCreate; e_colorfillDestroy; 0x8d778].
        pose proof FSH as SHD. split_at SHD 4%nat SHC4. split_at SHC4 1%nat SHC5. clear SHD SHC5.
        pose proof FR as FRrec. split_before FRrec (C8 s0) FRrec5. clear FRrec.
        at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                            repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
        pose proof DESTROY as DY. unfold pixDestroy_cps in DY.
        eapply cps_seq.
        { eapply DY with (lo := lo) (pp := fr + 32) (pix := pix) (v := v) (cv := cv) (ras := [RA_TOP]); rt_side idtac.
          all: lazymatch goal with
               | |- optrL _ _ _ _ _ _ =>
                   unfold optrL, parked in *; split;
                   [ right; exists fr, 1%nat; rewrite FRS3; change (fs_size 1) with 128;
                     split; [left; reflexivity|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
                     split; [lia|]; split; [lia|];
                     replace (shad (fr + 32)) with (fr / 8 + 2147450884) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
                     destruct SHC4 as [[_ B] _]; exact B
                   | unfold SEGTOP_A; repeat split; first [lia | clear - FR64; Z.div_mod_to_equations; lia] ]
               | |- rw_cells _ _ _ [C8 _] => exact PPC2
               | |- pix_obj _ _ _ _ _ => exact POBJ3
               | |- uctx _ _ _ _ =>
                   unfold uctx; rewrite !unsigned_lit by lia; unfold parked in S0INV;
                   apply chain_ok_push with (fp1 := bv_unsigned s0);
                     [ lia | clear - SPA; Z.div_mod_to_equations; lia | unfold USTACK_TOP; lia | unfold RA_TOP; lia | apply bv_unsigned_in_range
                     | rewrite Z_to_bv_bv_unsigned; rewrite <- RATOP; rewrite Z_to_bv_bv_unsigned;
                       lazymatch type of FRrec5 with rw_cells _ _ ?a _ => replace (usp + -16) with a by lia end; exact FRrec5
                     | cbn [chain_ok]; unfold link_invalid; lia ]
               | |- Forall _ _ => exact tr_destroy
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- lres _ _ _ _ _ =>
                   unfold lres, RASTER_COST, FRAMES_MAX, LIVE_MAX in *; rewrite FRS3, FR0; cbn [length];
                   split; [lia| split; [rewrite LV3; repeat match goal with H : rt_live RT _ = rt_live RT _ |- _ => rewrite H in * end; lia|
                   split; [repeat match goal with H : rt_credit RT _ = _ |- _ => rewrite H in * end; lia| exact LVP3]]]
               | |- ?g => idtac "LEFT-DY:" g
               end. }
        clear SHC4.
        after_call RT AF.
        lazymatch goal with H : rt_live RT _ = live_destroy pix v cv _ |- _ => rewrite LV3, LVE in H end.
        fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]|
                                        cbn [outside]; destruct (NFA _ Hx) as [N1 N2]; split; [lia| exact I]]).
        clear POBJ3 PIN3 PIN IN NCP LV3 LVP3.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
        walk_to AF MST [(usp - 96, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_stack_malloc 1%nat; e_pixDeserialize; e_pixDestroy; e_colorfillCreate; e_colorfillDestroy; 0x8d778].
        frame_release_g RT AF GP MST Σ fr 1%nat 128 PF AGF PFS usp lo 0x8d780
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
  - (* [comment removed for export] *)
    carve_frame 112%nat ST.
    walk_to AF MST [(usp - 112, usp)] [e_stack_malloc 1%nat; e_pixDeserialize; e_pixDestroy; e_colorfillCreate; e_colorfillDestroy].
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
      walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_stack_malloc 1%nat; e_pixDeserialize; e_pixDestroy; e_colorfillCreate; e_colorfillDestroy; 0x8d778].
      frame_release_raw RT AF GP MST Σ fr 1%nat 128 PF AGF PFS usp lo 0x8d780
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
      walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16); (855552, 855560)]
                   [e_stack_malloc 1%nat; e_pixDeserialize; e_pixDestroy; e_colorfillCreate; e_colorfillDestroy; 0x8d778].
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
        walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_stack_malloc 1%nat; e_pixDeserialize; e_pixDestroy; e_colorfillCreate; e_colorfillDestroy; 0x8d778].
        frame_release_g RT AF GP MST Σ fr 1%nat 128 PF AGF PFS usp lo 0x8d780
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
        pose proof POBJ as (PXC & (PIN & PX0 & PX16 & _) & _).
        chunk_facts RT AF GP pix 64.
        lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ =>
          assert (NCP : forall a, PF a -> a < pix \/ pix + 64 <= a)
            by (intros a [Ha _]; apply (inner_chunk_apart RT AF S mm pix 64 (rt_live RT Σ) (rt_frames RT Σ) usp a A PIN);
                [ intros e He; apply (live_destroy_in pix v cv); rewrite LVE;
                  repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact He
                | intros e He; rewrite FR0 in He; destruct He
                | repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul
                | exact Ha ]) end.
        lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ =>
          assert (FRSh : rt_frames RT S = (fr, 1%nat) :: rt_frames RT Σ)
            by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity) end.
        fframe_chunk RT AF fr 1%nat 128 pix 64. norm_fshadow.
        unfold pix_cells in PXC. hide POBJ.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
        walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)]
                     [e_stack_malloc 1%nat; e_pixDeserialize; e_pixDestroy; e_colorfillCreate; e_colorfillDestroy; 0x8d778].
        unfold hid in POBJ.
        lazymatch goal with A : ART RT ?S ?m0, MUx : munch _ ?m0 ?m1 |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
          assert (KL1 : keeps_live (rt_live RT S) m0 m1)
            by (apply (keeps_live_walk1 RT AF S m0 m1 fr usp (usp + -112) A ltac:(rewrite FRSh; left; reflexivity)
                         ltac:(repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; unfold STACK_WIN; lia) MUx));
          pose proof (pix_obj_keep _ m0 m1 pix v cv KL1 POBJ) as POBJ'; clear KL1 end.
        clear POBJ.
        pose proof FR as FRrec. split_before FRrec (C8 s0) FRrec3. clear FRrec.
        at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                            repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
        pose proof CFC as CC. unfold l_colorfillCreate_cps in CC.
        eapply cps_seq.
        { eapply CC with (lo := lo) (pix := pix) (v := v) (cv := cv) (ras := [RA_TOP]); rt_side idtac.
          - unfold uctx. rewrite !unsigned_lit by lia. unfold parked in S0INV.
            apply chain_ok_push with (fp1 := bv_unsigned s0);
              [ lia | clear - SPA; Z.div_mod_to_equations; lia | unfold USTACK_TOP; lia | unfold RA_TOP; lia | apply bv_unsigned_in_range | | cbn [chain_ok]; unfold link_invalid; lia ].
            rewrite Z_to_bv_bv_unsigned. rewrite <- RATOP. rewrite Z_to_bv_bv_unsigned.
            lazymatch type of FRrec3 with rw_cells _ _ ?a _ => replace (usp + -16) with a by lia end. exact FRrec3.
          - exact tr_cfcreate.
          - lenv_tac.
          - unfold lres, RASTER_COST, FRAMES_MAX, LIVE_MAX in *. rewrite FRSh, FR0. cbn [length].
            lazymatch goal with LB : Z.of_nat (length (rt_live RT ?S)) <= Z.of_nat (length (rt_live RT ?S0)) + 4, LP : forall p n, In (p, n) (rt_live RT ?S) -> 0 < n |- _ =>
              repeat match goal with H : rt_live RT S0 = _ |- _ => rewrite H in LB end;
              repeat match goal with H : rt_credit RT _ = _ |- _ => rewrite H in * end;
              split; [lia| split; [lia| split; [lia| exact LP]]] end. }
        after_call RT AF.
        lazymatch goal with H : ?c = 0 -> rw_cells _ _ pix _ |- _ => rename H into CF0; set (cf := c) in * end.
        lazymatch goal with H : cf <> 0 -> _ |- _ => rename H into CFN end.
        lazymatch goal with H : rt_live RT _ = (if cf =? 0 then _ else _) |- _ => rename H into LV2 end.
        lazymatch type of CFN with _ -> cf_obj _ _ _ ?c /\ _ => set (cfc := c) in * end.
        match goal with H : rt_credit RT _ - 2 <= rt_credit RT _ |- _ => rename H into CR2 end.
        (* [comment removed for export] *)
        lazymatch goal with AGx : agree_on _ ?ma ?mb, A : ART RT ?S ?ma |- cps _ (ASTA RT _ _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
          assert (KC2 : keeps_cmap v ma mb)
            by (apply (keeps_cmap_of_agree _ _ _ _ _ v cv _ ma mb pix POBJ' AGx (fun e He => He)); intros NZ CIN zx Hzx;
                assert (NE1 : p_cmap v <> pix) by (destruct POBJ' as (_ & _ & _ & _ & [CZ0|(_ & NE1 & _)]); [contradiction| exact NE1]);
                pose proof (live_apart RT AF S ma (p_cmap v) 24 pix 64 A CIN PIN NE1) as D; cbn [outside]; split; [clear - D Hzx; lia| exact I]) end.
        fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx));
                                          [ intros e He; apply (fun l H => proj1 (live_destroy_in pix v cv l e H)); rewrite LVE;
                                            repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact He
                                          | solve [frames_sub_tac] | lia]
                                       | cbn [outside]; pose proof (NCP _ Hx) as HxN; split; [clear - HxN; lia| exact I]]).
        (* [comment removed for export] *)
        lazymatch goal with A : ART RT ?S2 ?mm |- cps _ (ASTA RT ?S2 _ _) _ =>
          lazymatch type of PIN with In _ (rt_live RT ?S1) =>
            assert (SUB12 : forall e, In e (rt_live RT S1) -> In e (rt_live RT S2))
              by (intros e He; rewrite LV2; destruct (Z.eqb_spec cf 0) as [CZ|CNZ]; [exact He| rewrite cf_live_app; apply in_or_app; right; exact He]);
            assert (LVP2 : forall p n, In (p, n) (rt_live RT S2) -> 0 < n)
              by (intros p n Hin; rewrite LV2 in Hin; destruct (Z.eqb_spec cf 0) as [CZ|CNZ]; [exact (LVP1 p n Hin)|];
                  rewrite cf_live_app in Hin; apply in_app_or in Hin; destruct Hin as [Hin|Hin]; [| exact (LVP1 p n Hin)];
                  cbn [cf_live In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; clear; lia|]); destruct Hin);
            assert (LEN2 : Z.of_nat (length (rt_live RT S2)) <= Z.of_nat (length (rt_live RT S1)) + 12)
              by (rewrite LV2; destruct (Z.eqb_spec cf 0) as [CZ|CNZ]; [clear; lia| cbn [cf_live length]; clear; lia]);
            assert (FRS2 : rt_frames RT S2 = (fr, 1%nat) :: rt_frames RT Σ)
              by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity)
          end end.
        pose proof (SUB12 _ PIN) as PIN2.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
        walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)]
                     [e_stack_malloc 1%nat; e_pixDeserialize; e_pixDestroy; e_colorfillCreate; e_colorfillDestroy; 0x8d778].
        lazymatch goal with A : ART RT ?S ?m0, MUx : munch _ ?m0 ?m1 |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
          assert (KL3 : keeps_live (rt_live RT S) m0 m1)
            by (apply (keeps_live_walk1 RT AF S m0 m1 fr usp (usp + -112) A ltac:(rewrite FRS2; left; reflexivity)
                         ltac:(repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; unfold STACK_WIN; lia) MUx));
          assert (KC3 : keeps_cmap v m0 m1) by (exact (keeps_cmap_of_live _ _ v cv _ m0 m1 pix POBJ' SUB12 KL3));
          (* [comment removed for export] *)
          assert (PRE : cf = 0 \/ (cf_obj (rt_live RT S) m1 cf cfc /\ cf_pix cfc = pix /\ pix_obj_rc (rt_live RT S) m1 pix v cv 2
                                   /\ ~ In pix (map fst (cf_live cf cfc []))))
            by (destruct (Z.eq_dec cf 0) as [CZ|CNZ]; [left; exact CZ| right];
                destruct (CFN CNZ) as (CFO & CFP & PXC2);
                split; [exact (cf_obj_keep_all _ m0 m1 cf cfc CFO KL3)|]; split; [exact CFP|]; split;
                [ apply (pix_obj_rc_rebuild _ _ _ m1 pix v cv 2 POBJ' SUB12);
                  [ exact (keeps_live_cells _ m0 m1 pix 64 pix (pix_cells_rc v 2) KL3 PIN2 ltac:(clear; lia) ltac:(cbn; clear; lia) PXC2)
                  | exact (keeps_cmap_trans v _ _ _ KC2 KC3) ]
                | pose proof (live_nodup RT AF S m0 A LVP2) as ND; rewrite LV2 in ND;
                  replace (cf =? 0) with false in ND by (symmetry; apply Z.eqb_neq; exact CNZ);
                  rewrite cf_live_app, map_app in ND;
                  exact (nodup_app_notin _ _ pix ND (in_map fst _ _ PIN)) ]);
          (* [comment removed for export] *)
          assert (PXCZ : cf = 0 -> rw_cells asegs m1 pix (pix_cells_rc v 1))
            by (intros CZ; exact (keeps_live_cells _ m0 m1 pix 64 pix (pix_cells_rc v 1) KL3 PIN2 ltac:(clear; lia) ltac:(cbn; clear; lia) (CF0 CZ)))
        end.
        (* [comment removed for export] *)
        split_at FRM 4%nat PPC2. split_at PPC2 1%nat FRMb. split_at FRMb 1%nat PPCF. split_at PPCF 1%nat FRMc.
        pose proof FSH as SHC. split_at SHC 8%nat SHC8. split_at SHC8 1%nat SHC9. clear SHC SHC9.
        at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                            repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
        pose proof CFD as CD. unfold l_colorfillDestroy_cps in CD.
        eapply cps_seq.
        { eapply CD with (lo := lo) (pp := fr + 64) (cf := cf) (pix := pix) (c := cfc) (v := v) (cv := cv); rt_side idtac.
          all: lazymatch goal with
               | |- optrF _ _ _ _ _ =>
                   unfold optrF, own_frame, parked in *; split;
                   [ exists fr, 1%nat; rewrite FRS2; change (fs_size 1) with 128;
                     split; [left; reflexivity|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
                     split; [lia|]; split; [lia|];
                     replace (shad (fr + 64)) with (fr / 8 + 2147450888) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
                     destruct SHC8 as [[_ B] _]; exact B
                   | unfold SEGTOP_A; repeat split; first [lia | clear - FR64; Z.div_mod_to_equations; lia] ]
               | |- rw_cells _ _ _ [C8 _] => exact PPCF
               | |- _ \/ _ => exact PRE
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- lres _ _ _ _ _ =>
                   unfold lres, RASTER_COST, FRAMES_MAX, LIVE_MAX in *; rewrite FRS2, FR0; cbn [length];
                   repeat match goal with H : rt_live RT _ = rt_live RT _ |- _ => rewrite H in * end;
                   repeat match goal with H : rt_credit RT _ = _ |- _ => rewrite H in * end;
                   split; [lia| split; [lia| split; [lia| exact LVP2]]]
               | |- ?g => idtac "LEFT-CFD:" g
               end. }
        clear SHC8.
        after_call RT AF.
        lazymatch goal with H : cf = 0 -> rt_pres_fp _ _ _ _ _ _ |- _ => rename H into KEEP0 end.
        lazymatch goal with H : cf <> 0 -> rt_pres_fp _ _ _ _ _ _ /\ _ |- _ => rename H into KEEPN end.
        lazymatch goal with H : rt_live RT _ = (if cf =? 0 then _ else cf_live_destroy _ _ _) |- _ => rename H into LV3raw end.
        match goal with H : rt_credit RT _ - 2 <= rt_credit RT _ |- _ => lazymatch H with CR2 => fail | _ => rename H into CR3 end end.
        (* [comment removed for export] *)
        lazymatch type of LVP2 with forall p n, In _ (rt_live RT ?S2) -> _ =>
          lazymatch type of PIN with In _ (rt_live RT ?S1) =>
            match goal with A : ART RT S2 ?mm |- _ =>
              assert (NDN : cf <> 0 -> List.NoDup (map fst (cf_live cf cfc []) ++ map fst (rt_live RT S1)))
                by (intros CNZ; pose proof (live_nodup RT AF S2 mm A LVP2) as ND; rewrite LV2 in ND;
                    replace (cf =? 0) with false in ND by (symmetry; apply Z.eqb_neq; exact CNZ);
                    rewrite cf_live_app, map_app in ND; exact ND) end end end.
        (* [comment removed for export] *)
        lazymatch type of KEEP0 with _ -> rt_pres_fp (rt_live RT ?S3) ?frs ?spc _ ?ma ?mb =>
          lazymatch type of PIN with In _ (rt_live RT ?S1) =>
            assert (LV3 : rt_live RT S3 = rt_live RT S1)
              by (rewrite LV3raw, LV2; destruct (Z.eqb_spec cf 0) as [CZ|CNZ]; [reflexivity|];
                  destruct (CFN CNZ) as ((_ & _ & _ & _ & _ & _ & CND) & _);
                  apply (cf_live_roundtrip cf cfc _ CND); intros e He;
                  exact (nodup_app_notin _ _ (fst e) (NDN CNZ) (in_map fst _ _ He)));
            assert (P : rt_pres_fp (rt_live RT S3) frs spc [(fr + 64, fr + 64 + 8); (pix + 20, pix + 24)] ma mb)
              by (destruct (Z.eq_dec cf 0) as [CZ|CNZ]; [intros a Ha _; exact (KEEP0 CZ a Ha I)| exact (proj1 (KEEPN CNZ))]);
            assert (PXC3 : rw_cells asegs mb pix (pix_cells v))
              by (destruct (Z.eq_dec cf 0) as [CZ|CNZ]; [| exact (proj2 (proj2 (KEEPN CNZ)))];
                  apply (rw_cells_agree_nw asegs ma mb _ _ (PXCZ CZ)); intros a Ha; apply (KEEP0 CZ); [| exact I];
                  right; right; left; exists pix, 64; split; [rewrite LV3; exact PIN| cbn in Ha; clear - Ha; lia])
          end end.
        lazymatch type of P with rt_pres_fp ?lv ?frs ?spc ?W ?ma ?mb =>
          assert (AG : agree_on (fun a => aclient lv frs spc a /\ outside W a) ma mb) by (intros ? [Ha Hb]; exact (P _ Ha Hb));
          clear P; rt_transport ma mb AG ltac:(fun A => split; [acl_dispatch A | outside_side]) end.
        lazymatch type of AG with agree_on _ ?ma ?mb =>
          lazymatch type of PIN with In _ (rt_live RT ?S1) =>
            match goal with A : ART RT S1 ?mm |- _ =>
              assert (KC4 : keeps_cmap v ma mb)
                by (apply (keeps_cmap_of_agree _ _ _ _ _ v cv _ ma mb pix POBJ' AG ltac:(intros e He; rewrite LV3; exact He)); intros NZ CIN zx Hzx;
                    assert (NE1 : p_cmap v <> pix) by (destruct POBJ' as (_ & _ & _ & _ & [CZ0|(_ & NE1 & _)]); [contradiction| exact NE1]);
                    exact (chunk_outside_local RT AF S1 mm fr 1%nat (p_cmap v) 24 (fr + 64) (fr + 64 + 8) pix zx A
                             ltac:(rewrite FRSh; left; reflexivity) ltac:(clear; lia) ltac:(change (fs_size 1) with 128; clear; lia) CIN PIN NE1 Hzx)) end end end.
        fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx));
                                          [ intros e He; rewrite LV3; apply (fun l H => proj1 (live_destroy_in pix v cv l e H)); rewrite LVE;
                                            repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact He
                                          | solve [frames_sub_tac] | lia]
                                       | cbn [outside]; pose proof (NCP _ Hx) as HxN; destruct (NFA _ Hx) as [HxF _];
                                         split; [clear - HxF; lia| split; [clear - HxN; lia| exact I]]]).
        lazymatch goal with A : ART RT ?S3 ?mb |- cps _ (ASTA RT ?S3 _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
          assert (POBJ3 : pix_obj (rt_live RT S3) mb pix v cv)
            by (apply pix_obj_rc_1; apply (pix_obj_rc_rebuild _ _ _ mb pix v cv 1 POBJ');
                [ intros e He; rewrite LV3; exact He | exact PXC3
                | exact (keeps_cmap_trans v _ _ _ KC2 (keeps_cmap_trans v _ _ _ KC3 KC4)) ]);
          assert (FRS3 : rt_frames RT S3 = (fr, 1%nat) :: rt_frames RT Σ)
            by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity);
          assert (LVP3 : forall p n, In (p, n) (rt_live RT S3) -> 0 < n) by (rewrite LV3; exact LVP1);
          assert (PIN3 : In (pix, 64) (rt_live RT S3)) by (rewrite LV3; exact PIN) end.
        clear LV3raw KEEP0 KEEPN PRE PXCZ NDN LV2 CF0 CFN SUB12 LVP2 LEN2 PIN2 KC2 KC3 KC4 POBJ'.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
        walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)]
                     [e_stack_malloc 1%nat; e_pixDeserialize; e_pixDestroy; e_colorfillCreate; e_colorfillDestroy; 0x8d778].
        pose proof FSH as SHD. split_at SHD 4%nat SHC4. split_at SHC4 1%nat SHC5. clear SHD SHC5.
        pose proof FR as FRrec. split_before FRrec (C8 s0) FRrec5. clear FRrec.
        at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                            repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
        pose proof DESTROY as DY. unfold pixDestroy_cps in DY.
        eapply cps_seq.
        { eapply DY with (lo := lo) (pp := fr + 32) (pix := pix) (v := v) (cv := cv) (ras := [RA_TOP]); rt_side idtac.
          all: lazymatch goal with
               | |- optrL _ _ _ _ _ _ =>
                   unfold optrL, parked in *; split;
                   [ right; exists fr, 1%nat; rewrite FRS3; change (fs_size 1) with 128;
                     split; [left; reflexivity|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
                     split; [lia|]; split; [lia|];
                     replace (shad (fr + 32)) with (fr / 8 + 2147450884) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
                     destruct SHC4 as [[_ B] _]; exact B
                   | unfold SEGTOP_A; repeat split; first [lia | clear - FR64; Z.div_mod_to_equations; lia] ]
               | |- rw_cells _ _ _ [C8 _] => exact PPC2
               | |- pix_obj _ _ _ _ _ => exact POBJ3
               | |- uctx _ _ _ _ =>
                   unfold uctx; rewrite !unsigned_lit by lia; unfold parked in S0INV;
                   apply chain_ok_push with (fp1 := bv_unsigned s0);
                     [ lia | clear - SPA; Z.div_mod_to_equations; lia | unfold USTACK_TOP; lia | unfold RA_TOP; lia | apply bv_unsigned_in_range
                     | rewrite Z_to_bv_bv_unsigned; rewrite <- RATOP; rewrite Z_to_bv_bv_unsigned;
                       lazymatch type of FRrec5 with rw_cells _ _ ?a _ => replace (usp + -16) with a by lia end; exact FRrec5
                     | cbn [chain_ok]; unfold link_invalid; lia ]
               | |- Forall _ _ => exact tr_destroy
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- lres _ _ _ _ _ =>
                   unfold lres, RASTER_COST, FRAMES_MAX, LIVE_MAX in *; rewrite FRS3, FR0; cbn [length];
                   split; [lia| split; [rewrite LV3; repeat match goal with H : rt_live RT _ = rt_live RT _ |- _ => rewrite H in * end; lia|
                   split; [repeat match goal with H : rt_credit RT _ = _ |- _ => rewrite H in * end; lia| exact LVP3]]]
               | |- ?g => idtac "LEFT-DY:" g
               end. }
        clear SHC4.
        after_call RT AF.
        lazymatch goal with H : rt_live RT _ = live_destroy pix v cv _ |- _ => rewrite LV3, LVE in H end.
        fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]|
                                        cbn [outside]; destruct (NFA _ Hx) as [N1 N2]; split; [lia| exact I]]).
        clear POBJ3 PIN3 PIN IN NCP LV3 LVP3.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
        walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_stack_malloc 1%nat; e_pixDeserialize; e_pixDestroy; e_colorfillCreate; e_colorfillDestroy; 0x8d778].
        frame_release_g RT AF GP MST Σ fr 1%nat 128 PF AGF PFS usp lo 0x8d780
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
Qed.
End CFFUZZ.
