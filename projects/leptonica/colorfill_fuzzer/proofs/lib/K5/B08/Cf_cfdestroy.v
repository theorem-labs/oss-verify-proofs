(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.B08 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit Lept_chain Lept_leaf Lept_objkit Cf_iface Cf_kit LeptB_guard.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Lemma tr_cf_free : In [0x9418c] CLIENT_TRACES.
Proof. vm_compute. tauto. Qed.

(* [comment removed for export] *)
Ltac cfd_ivt := cbn [ivls_client]; let zz := fresh "zz" in let Hzz := fresh "Hzz" in split; [intros zz Hzz; left; ul| exact I].
Ltac cfd_optr cf CKS CKH :=
  unfold optr, optrL; split; [left; exists cf, 88; split; [solve [in_live_tac]| lia]|];
  unpark CKS; unpark CKH; unfold SEGTOP_A; repeat split; lia.
(* [comment removed for export] *)
Ltac cfd_fold LVF PFCF usp :=
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx));
                                   [ solve [let e := fresh "e" in let He := fresh "He" in intros e He;
                                            repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end;
                                            unfold LVF, cf_live_destroy in He; repeat first [exact He | apply live_remove_sub in He]]
                                   | solve [frames_sub_tac] | lia]
                                 | let HC := fresh "HC" in let HO := fresh "HO" in
                                   cbn [outside]; pose proof (PFCF _ Hx) as HC; pose proof (proj2 Hx) as HO; cbn [outside] in HO;
                                   repeat split; try exact I; first [lia | tauto]]).
Ltac cfd_stops := constr:([0x905d0; 0x8efb8; 0x8e8fc; 0x8e3a4; 0x8dedc; 0x5ede4]).

Section CFDESTROY.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis PDRC : pixDestroy_rc_cps RT.
Hypothesis PDN : pixDestroy_null_cps RT.
Hypothesis BDO : boxaDestroy_one_cps RT.
Hypothesis PAN : pixaDestroy_null_cps RT.
Hypothesis NAD : numaaDestroy_cps RT.
Hypothesis DAD : l_dnaaDestroy_cps RT.
Hypothesis PAD : pixaDestroy_cps RT.

Theorem l_colorfillDestroy_ok : l_colorfillDestroy_cps RT.
Proof using AF GP PDRC PDN BDO PAN NAD DAD PAD.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pp cf pix c v cv
    FDO MST -> -> OPP PPC HCF ENV RES.
  unfold lpost, lpost_f, lenv, lres, keeps, keepsL in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct RES as (FRB & LVB & CRB & LVP).
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, e_colorfillDestroy, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold LSTK, STDERR_STACK in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  pose proof ST as (STa & STb & _).
  pose proof OPP as (OWNF & PP0 & PP8 & PPSH & PPSEG). unfold SEGTOP_A in PPSEG.
  assert (OWN : accok (@nil (Z * Z)) (rt_frames RT Σ) m pp 8) by (right; exact OWNF).   (* [comment removed for export] *)
  set (PF := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a).
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a Ha. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]. }
  assert (PPLO : pp + 8 <= lo /\ pp + 16 <= 2^47).
  { destruct OWNF as (ff & kk & HFin & HF1 & HF2 & _ & _ & HFT & _).
    pose proof (af_frames_range RT AF Σ m ff kk ART0 HFin) as (_ & R & _). unfold STACK_WIN in R. clear - HF1 HF2 HFT R LOW. lia. }
  destruct PPLO as [PPLO PPT].
  (* [comment removed for export] *)
  assert (LOUT : forall b k, In (b, k) (rt_live RT Σ) -> forall x, b <= x < b + k -> x < lo).
  { intros b k Hb x Hx. pose proof (af_live_range RT AF Σ m b k ART0 Hb) as LR. unfold STACK_WIN in LR. lia. }
  destruct HCF as [CF0|(CFO & CFP & POBJ & NIN)].
  - (* [comment removed for export] *)
    subst cf. refresh RT AF.
    walk_to AF MST [(usp - 32, usp)] (@nil Z).
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I]).
    lazymatch goal with MUx : munch _ ?mm ?mc |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]) end.
    apply cps_finish. intros c0 Hc. subst QF. cbv beta.
    lazymatch type of Hc with ASTA RT ?S' _ _ _ => exists S' end. eexists.
    split.
    { eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-. eexists.
      split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
      split; [split; [split; [assumption| split; assumption]| split; assumption]|].
      split; [intros _ a Ha _; apply AGF; exact Ha| intros HH; contradiction]. }
    change (0 =? 0) with true. cbv iota. repeat split; try reflexivity; lia.
  - (* [comment removed for export] *)
    destruct CFO as ((pad & CFC) & CFCH & BOXA & NAA & DNAA & PIXA & ND).
    pose proof CFCH as (CFIN & CF0 & CF16 & _).
    chunk_facts RT AF GP cf 88.
    unfold cf_cells in CFC. rewrite CFP in CFC.
    split_at CFC 1%nat CF1. split_at CF1 1%nat CF2. split_at CF2 6%nat CF3. split_at CF3 1%nat CF4. split_at CF4 1%nat CF5.
    split_at CF5 1%nat CF6. split_at CF6 1%nat CF7. split_at CF7 1%nat CF8.
    refresh RT AF.   (* [comment removed for export] *)
    (* [comment removed for export] *)
    pose proof POBJ as (_ & (IPIX & _) & _).
    assert (NDP : List.NoDup (pix :: map fst (cf_live cf c []))) by (apply List.NoDup_cons; assumption).
    cbn [map fst cf_live] in NDP. pose_neqs NDP. clear NDP ND NIN.
    pose proof BOXA as (_ & (IBA & _) & (IBARR & _) & _ & (_ & (IBOX & _)) & _).
    pose proof NAA as (_ & (INAA & _) & (INAARR & _) & _). pose proof DNAA as (_ & (IDNAA & _) & (IDNARR & _) & _).
    pose proof PIXA as (_ & (IPA & _) & (IPARR & _) & (_ & (IPBA & _) & (IPBARR & _) & _) & _).
    assert (APX : cf + 88 <= pix \/ pix + 64 <= cf) by (apply (live_apart RT AF Σ m cf 88 pix 64 ART0 CFIN IPIX); neq_tac).
    repeat match goal with
    | H : In (?q, ?k) (rt_live RT Σ) |- _ =>
        lazymatch q with cf => fail | pix => fail | _ =>
          lazymatch goal with _ : apartp q k cf 88 |- _ => fail | _ => idtac end;
          let A1 := fresh "APC" in let A2 := fresh "APP" in
          assert (A1 : apartp q k cf 88) by (exact (live_apart RT AF Σ m q k cf 88 ART0 H CFIN ltac:(neq_tac)));
          assert (A2 : apartp q k pix 64) by (exact (live_apart RT AF Σ m q k pix 64 ART0 H IPIX ltac:(neq_tac)))
        end
    end.
    chunk_facts RT AF GP pix 64.
    (* [comment removed for export] *)
    assert (PPX : (pp + 8 <= pix \/ pix + 64 <= pp) /\ (pp + 8 <= cf \/ cf + 88 <= pp)).
    { destruct OWNF as (ff & kk & HFin & HF1 & HF2 & _).
      pose proof (af_frames_range RT AF Σ m ff kk ART0 HFin) as (_ & _ & _ & DD).
      pose proof (DD pix 64 IPIX) as DP. pose proof (DD cf 88 CFIN) as DC.
      clear - HF1 HF2 DP DC. lia. }
    destruct PPX as [PPX1 PPX2].
    (* [comment removed for export] *)
    clear AGF PFS. clear PF.
    set (LVF := cf_live_destroy cf c (rt_live RT Σ)).
    set (PF := fun a => aclient LVF (rt_frames RT Σ) usp a /\ outside [(pp, pp + 8); (pix + 20, pix + 24)] a).
    pose proof (agree_refl PF m) as AGF.
    assert (LVFS : forall e, In e LVF -> In e (rt_live RT Σ) /\ fst e <> cf) by (intros ee Hee; exact (cf_live_destroy_in cf c _ ee Hee)).
    assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
    { intros xa [HXa _]. apply (aclient_mono _ _ usp (rt_live RT Σ) (rt_frames RT Σ) usp) in HXa; [| intros ee Hee; exact (proj1 (LVFS ee Hee))| auto| lia].
      destruct (aclient_split RT AF Σ m usp xa ART0 HXa) as [HXS|HXS]; [left; exact HXS| right; unfold STACK_WIN in HXS; lia]. }
    assert (PFCF : forall a, PF a -> a < cf \/ cf + 88 <= a).
    { intros xa [HXa _]. apply (removed_chunk_apart RT AF Σ m cf 88 LVF usp xa ART0 CFIN LVFS); [unfold STACK_WIN; lia| exact HXa]. }
    park_disj.
    walk_to AF MST [(usp - 32, usp)] [0x905d0; 0x8efb8; 0x8e8fc; 0x8e3a4; 0x8dedc; 0x5ede4].
    lazymatch goal with MUx : munch _ m ?mc |- _ =>
      assert (K0 : keeps_live (rt_live RT Σ) m mc)
        by (let b := fresh "b" in let k := fresh "k" in let Hb := fresh "Hb" in let a := fresh "a" in let Ha := fresh "Ha" in
            intros b k Hb a Ha; apply MUx; cbn [outside]; split; [pose proof (LOUT b k Hb _ Ha); lia| exact I]) end.
    apply (fun h => pix_obj_rc_keep_all _ _ _ _ _ _ _ h K0) in POBJ.
    apply (fun h => boxa_one_keep_all _ _ _ _ _ _ _ _ _ _ h K0) in BOXA.
    apply (fun h => parr16_obj_keep_all _ _ _ _ _ _ h K0) in NAA. apply (fun h => parr16_obj_keep_all _ _ _ _ _ _ h K0) in DNAA.
    apply (fun h => pixa_obj_keep_all _ _ _ _ _ _ _ _ h K0) in PIXA. clear K0.
    (* [comment removed for export] *)
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
    pose proof PDRC as C1. unfold pixDestroy_rc_cps in C1.
    eapply cps_seq.
    { eapply C1 with (lo := lo) (pp := cf) (pix := pix) (v := v) (cv := cv) (rc := 2); rt_side idtac.
      all: lazymatch goal with
           | |- optr _ _ _ _ _ => unfold optr, optrL; split; [left; exists cf, 88; split; [solve [in_live_tac]| lia]|];
                                  unpark CKS; unpark CKH; unfold SEGTOP_A; repeat split; lia
           | |- _ \/ _ => unpark APX; lia
           | |- lenv _ _ _ _ _ _ => lenv_tac
           | |- lres _ _ _ _ _ => lres_tac
           end. }
    after_call RT AF.
    lazymatch goal with H : rw_cells asegs _ pix (pix_cells_rc v (2 - 1)) |- _ =>
      rename H into PXC; unfold pix_cells_rc in PXC; change (2 - 1) with 1 in PXC end.
    lazymatch goal with AGx : agree_on _ _ ?mb |- cps _ (ASTA RT ?S _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
      obj_keep RT S BOXA AGx; obj_keep RT S NAA AGx; obj_keep RT S DNAA AGx; obj_keep RT S PIXA AGx end.
    cfd_fold LVF PFCF usp.
    walk_to AF MST [(usp - 32, usp)] [0x905d0; 0x8efb8; 0x8e8fc; 0x8e3a4; 0x8dedc; 0x5ede4].
    (* [comment removed for export] *)
    at_call RT AF ltac:(cfd_ivt) ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
    pose proof PDN as C2. unfold pixDestroy_null_cps in C2.
    eapply cps_seq.
    { eapply C2 with (lo := lo) (pp := cf + 8); rt_side idtac.
      all: lazymatch goal with
           | |- optr _ _ _ _ _ => cfd_optr cf CKS CKH
           | |- rw_cells _ _ _ _ => exact CF1
           | |- lenv _ _ _ _ _ _ => lenv_tac
           | |- lres _ _ _ _ _ => lres_tac
           end. }
    after_call RT AF.
    lazymatch goal with AGx : agree_on _ _ ?mb |- cps _ (ASTA RT ?S _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
      obj_keep RT S BOXA AGx; obj_keep RT S NAA AGx; obj_keep RT S DNAA AGx; obj_keep RT S PIXA AGx end.
    cfd_fold LVF PFCF usp.
    walk_to AF MST [(usp - 32, usp)] [0x905d0; 0x8efb8; 0x8e8fc; 0x8e3a4; 0x8dedc; 0x5ede4].
    (* [comment removed for export] *)
    at_call RT AF ltac:(cfd_ivt) ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
    pose proof BDO as C3. unfold boxaDestroy_one_cps in C3.
    eapply cps_seq.
    { eapply C3 with (lo := lo) (pp := cf + 40) (ba := cf_boxas c) (arr := cf_barr c) (b := cf_box c); rt_side idtac.
      all: lazymatch goal with
           | |- optrL _ _ _ _ _ _ => cfd_optr cf CKS CKH
           | |- rw_cells _ _ _ _ => exact CF3
           | |- boxa_one _ _ _ _ _ _ _ _ _ => exact BOXA
           | |- lenv _ _ _ _ _ _ => lenv_tac
           | |- forall p n, In (p, n) _ -> 0 < n => lvp_tac LVP
           | |- ?g => idtac "LEFT3:" g
           end. }
    after_call RT AF.
    lazymatch goal with AGx : agree_on _ _ ?mb |- cps _ (ASTA RT ?S _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
      obj_keep RT S NAA AGx; obj_keep RT S DNAA AGx; obj_keep RT S PIXA AGx end.
    cfd_fold LVF PFCF usp.
    walk_to AF MST [(usp - 32, usp)] [0x905d0; 0x8efb8; 0x8e8fc; 0x8e3a4; 0x8dedc; 0x5ede4].
    (* [comment removed for export] *)
    at_call RT AF ltac:(cfd_ivt) ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
    pose proof PAN as C4. unfold pixaDestroy_null_cps in C4.
    eapply cps_seq.
    { eapply C4 with (lo := lo) (pp := cf + 48); rt_side idtac.
      all: lazymatch goal with
           | |- optr _ _ _ _ _ => cfd_optr cf CKS CKH
           | |- rw_cells _ _ _ _ => exact CF4
           | |- lenv _ _ _ _ _ _ => lenv_tac
           end. }
    after_call RT AF.
    lazymatch goal with AGx : agree_on _ _ ?mb |- cps _ (ASTA RT ?S _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
      obj_keep RT S NAA AGx; obj_keep RT S DNAA AGx; obj_keep RT S PIXA AGx end.
    cfd_fold LVF PFCF usp.
    walk_to AF MST [(usp - 32, usp)] [0x905d0; 0x8efb8; 0x8e8fc; 0x8e3a4; 0x8dedc; 0x5ede4].
    (* [comment removed for export] *)
    at_call RT AF ltac:(cfd_ivt) ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
    eapply cps_seq.
    { eapply C4 with (lo := lo) (pp := cf + 56); rt_side idtac.
      all: lazymatch goal with
           | |- optr _ _ _ _ _ => cfd_optr cf CKS CKH
           | |- rw_cells _ _ _ _ => exact CF5
           | |- lenv _ _ _ _ _ _ => lenv_tac
           end. }
    after_call RT AF.
    lazymatch goal with AGx : agree_on _ _ ?mb |- cps _ (ASTA RT ?S _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
      obj_keep RT S NAA AGx; obj_keep RT S DNAA AGx; obj_keep RT S PIXA AGx end.
    cfd_fold LVF PFCF usp.
    walk_to AF MST [(usp - 32, usp)] [0x905d0; 0x8efb8; 0x8e8fc; 0x8e3a4; 0x8dedc; 0x5ede4].
    (* [comment removed for export] *)
    at_call RT AF ltac:(cfd_ivt) ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
    pose proof NAD as C6. unfold numaaDestroy_cps, parr16Destroy_cps in C6.
    eapply cps_seq.
    { eapply C6 with (lo := lo) (pp := cf + 64) (o := cf_naa c) (arr := cf_naarr c); rt_side idtac.
      all: lazymatch goal with
           | |- optrL _ _ _ _ _ _ => cfd_optr cf CKS CKH
           | |- rw_cells _ _ _ _ => exact CF6
           | |- parr16_obj _ _ _ _ _ => exact NAA
           | |- lenv _ _ _ _ _ _ => lenv_tac
           | |- forall p n, In (p, n) _ -> 0 < n => lvp_tac LVP
           end. }
    after_call RT AF.
    lazymatch goal with AGx : agree_on _ _ ?mb |- cps _ (ASTA RT ?S _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
      obj_keep RT S DNAA AGx; obj_keep RT S PIXA AGx end.
    cfd_fold LVF PFCF usp.
    walk_to AF MST [(usp - 32, usp)] [0x905d0; 0x8efb8; 0x8e8fc; 0x8e3a4; 0x8dedc; 0x5ede4].
    (* [comment removed for export] *)
    at_call RT AF ltac:(cfd_ivt) ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
    pose proof DAD as C7. unfold l_dnaaDestroy_cps, parr16Destroy_cps in C7.
    eapply cps_seq.
    { eapply C7 with (lo := lo) (pp := cf + 72) (o := cf_dnaa c) (arr := cf_dnarr c); rt_side idtac.
      all: lazymatch goal with
           | |- optrL _ _ _ _ _ _ => cfd_optr cf CKS CKH
           | |- rw_cells _ _ _ _ => exact CF7
           | |- parr16_obj _ _ _ _ _ => exact DNAA
           | |- lenv _ _ _ _ _ _ => lenv_tac
           | |- forall p n, In (p, n) _ -> 0 < n => lvp_tac LVP
           end. }
    after_call RT AF.
    lazymatch goal with AGx : agree_on _ _ ?mb |- cps _ (ASTA RT ?S _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
      obj_keep RT S PIXA AGx end.
    cfd_fold LVF PFCF usp.
    walk_to AF MST [(usp - 32, usp)] [0x905d0; 0x8efb8; 0x8e8fc; 0x8e3a4; 0x8dedc; 0x5ede4].
    (* [comment removed for export] *)
    at_call RT AF ltac:(cfd_ivt) ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
    pose proof PAD as C8. unfold pixaDestroy_cps in C8.
    eapply cps_seq.
    { eapply C8 with (lo := lo) (pp := cf + 80) (pa := cf_pixa c) (parr := cf_parr c) (ba := cf_pba c) (barr := cf_pbarr c); rt_side idtac.
      all: lazymatch goal with
           | |- optrL _ _ _ _ _ _ => cfd_optr cf CKS CKH
           | |- rw_cells _ _ _ _ => exact CF8
           | |- pixa_obj _ _ _ _ _ _ _ => exact PIXA
           | |- lenv _ _ _ _ _ _ => lenv_tac
           | |- forall p n, In (p, n) _ -> 0 < n => lvp_tac LVP
           end. }
    after_call RT AF.
    cfd_fold LVF PFCF usp.
    walk_to AF MST [(usp - 32, usp)] [0x905d0; 0x8efb8; 0x8e8fc; 0x8e3a4; 0x8dedc; 0x5ede4].
    (* [comment removed for export] *)
    at_call RT AF ltac:(cfd_ivt) ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
    eapply cps_seq.
    { pose proof (gp_free RT GP) as FC; unfold free_contractC in FC; eapply FC with (lo := lo) (p := cf) (n := 88); rt_side idtac.
      all: lazymatch goal with
           | |- In _ _ => solve [in_live_tac]
           | |- unwind_okC _ _ _ _ => apply unwind_okC_of_ok; rewrite !unsigned_lit by ul; [exact tr_cf_free| left; ul]
           end. }
    after_call RT AF.

    fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx));
                             [ solve [let e := fresh "e" in let He := fresh "He" in intros e He;
                                      repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end;
                                      unfold LVF, cf_live_destroy in He; repeat first [exact He | apply live_remove_sub in He]]
                             | solve [frames_sub_tac] | lia]).
    repeat match goal with H : In (_, _) (rt_live RT Σ) |- _ => clear H end.
    refresh RT AF.
    walk_to AF MST [(usp - 32, usp); (pp, pp + 8)] (@nil Z).

    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; aclient_tac| exact I]]).
    lazymatch goal with MUx : munch _ ?mm ?mc |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
      agf_munch AGF MUx ltac:(fun Hx => let HO := fresh "HO" in cbn [outside]; pose proof (PFS _ Hx); pose proof (proj2 Hx) as HO;
                                        cbn [outside] in HO; repeat split; try exact I; first [lia | tauto]) end.
    apply cps_finish. intros c0 Hc. subst QF. cbv beta.
    lazymatch type of Hc with ASTA RT ?S' _ _ _ => exists S' end. eexists.
    split.
    { eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-. eexists.
      split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
      split; [split; [split; [assumption| split; assumption]| split; assumption]|].
      split; [intros E0; lia|]. intros _.
      split; [| split; [eassumption| unfold pix_cells_rc; exact PXC]].
      intros xa HXa HXo. apply AGF. split; [| exact HXo].
      repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H in HXa end. exact HXa. }

    replace (cf =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    split; [repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity|].
    split; [repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity|].
    split; [repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity|].
    repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end.
    repeat match goal with H : context [rt_credit RT _] |- _ => revert H end. clear. intros. lia.
Qed.
End CFDESTROY.
