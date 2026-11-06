(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.A10 Require Import ImageA.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.A10 Require Import Layout.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.A10 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit Lept_leaf LeptL_kit Gm_iface Fh_iface Fh_sel_iface Fh_statics Fh_selkit.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Lemma tr_selaDestroy_1 : In [0xa7160] CLIENT_TRACES. Proof. apply ct_mem_In; vm_compute; reflexivity. Qed.
Lemma tr_selaDestroy_2 : In [0xa7168] CLIENT_TRACES. Proof. apply ct_mem_In; vm_compute; reflexivity. Qed.

Section SELAD.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis SDS : selDestroy_cps RT.

Theorem selaDestroy_ok : selaDestroy_cps RT.
Proof using AF GP SDS.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pp sela arr sels l1 l2
    FDO MST -> -> OP PPC SAO SHAPE POS ENV.
  unfold lpost_f, lenv, keeps, keepsL, optrL in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct OP as (OWN & PP0 & PP8 & PPH & PPS).
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, e_selaDestroy, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold LSTK, STDERR_STACK in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  pose proof ST as (STa & STb & _).
  pose proof SAO as (SAC & (SAIN & SA0 & SA16 & _) & (ARIN & AR0 & AR16 & _) & L50 & ARRC & SELS).
  unfold sela_cells in SAC.
  set (n := Z.of_nat (length sels)) in *.
  set (LVF := live_remove_all (sela_frees sela arr sels) (rt_live RT Σ)) in *.
  assert (LVFS : forall e, In e LVF -> In e (rt_live RT Σ)) by (intros e He; apply live_remove_all_In in He; exact (proj1 He)).
  pose proof (live_nodup_all RT AF Σ m ART0 POS) as NDALL.
  assert (ACCP : acc asegs m pp 8).
  { apply (accok_acc_sub RT AF Σ m LVF (rt_frames RT Σ) pp 8 ART0 ltac:(lia) LVFS ltac:(auto) OWN). }
  assert (PPLO : pp + 8 <= lo).
  { destruct OWN as [(p & k & Hin & H1 & H2)|(f & k & Hin & H1 & H2 & _)].
    - pose proof (af_live_range RT AF Σ m p k ART0 (LVFS _ Hin)) as (_ & R & _). unfold STACK_WIN in R. lia.
    - pose proof (af_frames_range RT AF Σ m f k ART0 Hin) as (_ & R & _). unfold STACK_WIN in R. lia. }
  set (PF := fun a => aclient LVF (rt_frames RT Σ) usp a /\ outside [(pp, pp + 8)] a).
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a [Ha _]. destruct (aclient_split RT AF Σ m usp a ART0) as [H|H]; [| left; exact H| right; unfold STACK_WIN in H; lia].
    apply (aclient_mono LVF (rt_frames RT Σ) usp _ _ usp a Ha); [exact LVFS| auto| lia]. }
  (* [comment removed for export] *)
  assert (PPAP : forall qq kk, In (qq, kk) (rt_live RT Σ) -> In qq (sela_frees sela arr sels) -> pp + 8 <= qq \/ qq + kk <= pp).
  { intros qq kk Hq Hf. destruct OWN as [(p & k & Hin & H1 & H2)|(f & k & Hin & H1 & H2 & _)].
    - apply live_remove_all_In in Hin. destruct Hin as (Hin & Hnf). cbn [fst] in Hnf.
      assert (NE : p <> qq) by (intros E; apply Hnf; rewrite E; exact Hf).
      pose proof (live_addr_disj RT AF Σ m p k qq kk ART0 Hin Hq NE). lia.
    - pose proof (af_frames_range RT AF Σ m f k ART0 Hin) as (_ & _ & _ & FL). specialize (FL qq kk Hq). lia. }
  assert (PPSEG : pp + 8 <= 65536 \/ 6578176 <= pp) by (clear - PPS; lia).
  assert (PPSH : pp + 8 <= 2147446784 \/ 17594333495296 <= pp) by (clear - PPH; lia).
  park OWN. hide SHAPE.
  chunk_facts RT AF GP sela 16. chunk_facts RT AF GP arr 400.
  assert (QSA : arr + 400 <= sela \/ sela + 16 <= arr).
  { assert (NE : arr <> sela) by (intros E; rewrite E in ARIN; pose proof (nodup_fst_inj _ _ _ _ NDALL ARIN SAIN); lia).
    exact (live_addr_disj RT AF Σ m arr 400 sela 16 ART0 ARIN SAIN NE). }
  refresh RT AF. unfold SHB in *. park_disj.
  walk_to AF MST [(usp - 96, usp)] [0xa710c; 0xa7148].
  assert (LVFEQ : LVF = l1 ++ l2).
  { unfold LVF. unfold hid in SHAPE. rewrite SHAPE. apply sela_destroy_live. rewrite <- SHAPE. exact NDALL. }
  assert (NESA : sela <> arr) by (unfold parked in QSA; clear - QSA; lia).
  assert (ARFR : In arr (sela_frees sela arr sels)) by (unfold sela_frees; apply in_or_app; right; left; reflexivity).
  assert (SAFR : In sela (sela_frees sela arr sels)) by (unfold sela_frees; apply in_or_app; right; right; left; reflexivity).
  assert (APARR : forall x, PF x -> x < arr \/ arr + 400 <= x).
  { intros x [Hx _]. exact (freed_chunk_apart RT AF Σ m _ _ usp arr 400 x ART0 eq_refl ltac:(ul) ARIN ARFR Hx). }
  assert (APSELA : forall x, PF x -> x < sela \/ sela + 16 <= x).
  { intros x [Hx _]. exact (freed_chunk_apart RT AF Σ m _ _ usp sela 16 x ART0 eq_refl ltac:(ul) SAIN SAFR Hx). }
  lazymatch goal with FRx : rw_cells asegs _ (usp + -96) ?frcs |- _ =>
  assert (TAIL : forall (Σk : rts RT) (mc : mem) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s6' s7' s8' s9' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32),
     hid (rt_live RT Σk = l1 ++ [(arr, 400); (sela, 16)] ++ l2) -> List.NoDup (map fst (rt_live RT Σk)) ->
     rt_frames RT Σk = rt_frames RT Σ -> rt_sp0 RT Σk = rt_sp0 RT Σ -> rt_credit RT Σ <= rt_credit RT Σk ->
     ART RT Σk mc -> mem_inv asegs mc -> stk asegs mc lo (usp + -96) -> LIBH mc -> io_ssp mc -> agree_on PF m mc ->
     rw_cells asegs mc (usp + -96) frcs ->
     rw_cells asegs mc sela [C4 (Z_to_bv 64 n); C4 (Z_to_bv 64 50); C8 (Z_to_bv 64 arr)] ->
     hid (rw_cells asegs mc pp [C8 (Z_to_bv 64 sela)]) ->
     cps asegs (ASTA RT Σk PMc (eq (MS (mkR ra' (Z_to_bv 64 (usp + -96)) gp (Z_to_bv 64 D_defs.TP_A) t0' t1' t2' (Z_to_bv 64 pp) (Z_to_bv 64 sela)
          a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (sela + 8)) (Z_to_bv 64 (pp / 8 + 2147450880)) (Z_to_bv 64 2147450880)
          (Z_to_bv 64 (sela / 8 + 2147450880)) s6' s7' s8' s9' s10 s11 t3' t4' t5' t6') F' (Z_to_bv 64 0xa7148) fc' None mc (seg_rom asegs)))) QF) end.
  { clear AGF.
    repeat match goal with H : rw_cells asegs _ _ _ |- _ => clear H end.
    repeat match goal with H : ro_cells asegs _ _ _ |- _ => clear H end.
    repeat match goal with H : bytes_at asegs _ _ _ |- _ => clear H end.
    repeat match goal with H : munch _ _ _ |- _ => clear H end.
    repeat match goal with H : acc asegs _ _ _ |- _ => clear H end.
    repeat match goal with H : ART RT _ _ |- _ => lazymatch type of H with ART RT Σ m => fail | _ => clear H end end.
    repeat match goal with H : wmono asegs _ _ |- _ => clear H end.
    repeat match goal with H : mem_inv asegs _ |- _ => clear H end.
    repeat match goal with H : stk asegs _ _ _ |- _ => clear H end.
    repeat match goal with H : LIBH _ |- _ => clear H end.
    repeat match goal with H : io_ssp _ |- _ => clear H end.
    clear SAO SELS.
    intros Σk mc ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s6' s7' s8' s9' t3' t4' t5' t6' F' fc'
      LVK NDk FRK SPK CRK ARTk MIk STk LHk SSPk AGFk FRc SAC PPC.
    assert (INAk : In (arr, 400) (rt_live RT Σk)) by (unfold hid in LVK; rewrite LVK; apply in_or_app; right; left; reflexivity).
    assert (INSk : In (sela, 16) (rt_live RT Σk)) by (unfold hid in LVK; rewrite LVK; apply in_or_app; right; right; left; reflexivity).
    assert (SUBk : forall e, In e LVF -> In e (rt_live RT Σk)).
    { intros e He. rewrite LVFEQ in He. unfold hid in LVK. rewrite LVK. apply in_app_or in He. apply in_or_app. destruct He as [He|He]; [left; exact He| right; right; right; exact He]. }
    refresh RT AF. unfold SHB in *. park_disj.
    walk_to AF MST [(usp - 96, usp)] [e_free].
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
    eapply cps_seq.
    { pose proof (gp_free RT GP) as FREE; unfold free_contractC in FREE.
      eapply FREE with (lo := lo) (p := arr) (n := 400); rt_side idtac.
      all: lazymatch goal with
           | |- In _ _ => exact INAk
           | |- call_ok _ _ _ _ _ => call_ok_tac
           | |- _ => idtac
           end.
      apply unwind_okC_of_ok; rewrite ?unsigned_lit by lia; [exact tr_selaDestroy_1| left; ul]. }
    after_call RT AF.
    lazymatch goal with H : rt_live RT ?S = live_remove arr _ |- _ => rename H into LVA; rename S into Σa end.
    assert (INSa : In (sela, 16) (rt_live RT Σa)) by (rewrite LVA; apply live_remove_keep; [exact INSk| cbn [fst]; exact NESA]).
    assert (SUBa : forall e, In e LVF -> In e (rt_live RT Σa)).
    { intros e He. rewrite LVA. apply live_remove_keep; [exact (SUBk e He)|]. apply live_remove_all_In in He. destruct He as (_ & He2).
      intros E. apply He2. rewrite E. exact ARFR. }
    lazymatch goal with AG : agree_on ?P2 ?ma ?m1 |- _ =>
      unfold hid in PPC;
      apply (rw_cells_agree_nw asegs ma m1 pp _) in PPC;
        [| eapply agree_sub; [exact AG|]; intros zz Hzz; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Hzz;
           unfold parked in OWN; apply (aclient_mono LVF (rt_frames RT Σ) (usp + -96) _ _ (usp + -96) zz (accok_aclient LVF (rt_frames RT Σ) m (usp + -96) pp 8 zz OWN ltac:(lia)));
           [exact SUBa| intros e He; repeat match goal with H : rt_frames RT _ = _ |- _ => rewrite H end; exact He| lia]] end.
    agf_call AGFk AG ltac:(fun Hx => destruct Hx as [Hx _]; apply (aclient_mono LVF _ usp _ _ _ _ Hx); [exact SUBa| intros e He; repeat match goal with H : rt_frames RT _ = _ |- _ => rewrite H end; exact He| lia]).
    clear AG INAk INSk SUBk.
    hide LVA. hide PPC.
    repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H in * end.
    unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
    refresh RT AF. unfold SHB in *. park_disj.
    walk_to AF MST [(usp - 96, usp)] [e_free].
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
    eapply cps_seq.
    { pose proof (gp_free RT GP) as FREE; unfold free_contractC in FREE.
      eapply FREE with (lo := lo) (p := sela) (n := 16); rt_side idtac.
      all: lazymatch goal with
           | |- In _ _ => exact INSa
           | |- call_ok _ _ _ _ _ => call_ok_tac
           | |- _ => idtac
           end.
      apply unwind_okC_of_ok; rewrite ?unsigned_lit by lia; [exact tr_selaDestroy_2| left; ul]. }
    repeat match goal with H : rw_cells asegs _ sela _ |- _ => clear H end.
    after_call RT AF.
    lazymatch goal with H : rt_live RT ?S = live_remove sela _ |- _ => rename H into LVS; rename S into Σs end.
    assert (SUBs : forall e, In e LVF -> In e (rt_live RT Σs)).
    { intros e He. rewrite LVS. apply live_remove_keep; [exact (SUBa e He)|]. apply live_remove_all_In in He. destruct He as (_ & He2).
      intros E. apply He2. rewrite E. exact SAFR. }
    lazymatch goal with AG : agree_on ?P2 ?ma ?m1 |- _ =>
      unfold hid in PPC;
      apply (rw_cells_agree_nw asegs ma m1 pp _) in PPC;
        [| eapply agree_sub; [exact AG|]; intros zz Hzz; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Hzz;
           unfold parked in OWN; apply (aclient_mono LVF (rt_frames RT Σ) (usp + -96) _ _ (usp + -96) zz (accok_aclient LVF (rt_frames RT Σ) m (usp + -96) pp 8 zz OWN ltac:(lia)));
           [exact SUBs| intros e He; repeat match goal with H : rt_frames RT _ = _ |- _ => rewrite H end; exact He| lia]] end.
    agf_call AGFk AG ltac:(fun Hx => destruct Hx as [Hx _]; apply (aclient_mono LVF _ usp _ _ _ _ Hx); [exact SUBs| intros e He; repeat match goal with H : rt_frames RT _ = _ |- _ => rewrite H end; exact He| lia]).
    clear AG INSa SUBa.
    assert (LVFIN : rt_live RT Σs = LVF).
    { unfold hid in LVS, LVA, LVK. rewrite LVS, LVA, LVFEQ.
      change (live_remove sela (live_remove arr (rt_live RT Σk))) with (live_remove_all [arr; sela] (rt_live RT Σk)).
      rewrite LVK. apply live_remove_all_mid; [rewrite <- LVK; exact NDk| intros p; cbn [map fst In]; tauto]. }
    hide LVS. hide LVFIN.
    (* [comment removed for export] *)
    lazymatch type of AGFk with agree_on _ _ ?mcur =>
      assert (OWNc : accok LVF (rt_frames RT Σ) mcur pp 8) end.
    { unfold parked in OWN, PPSH. apply (accok_keep_fp LVF (rt_frames RT Σ) m _ LVF (rt_frames RT Σ) usp [(pp, pp + 8)] pp 8 OWN AGFk ltac:(lia) ltac:(auto)).
      intros zz Hzz. cbn [outside]. unfold shad, SHB in Hzz. split; [| exact I]. clear - Hzz PPSH PP0. Z.div_mod_to_equations. lia. }
    lazymatch goal with A : ART RT Σs ?mm |- _ =>
      assert (ACCPc : acc asegs mm pp 8) by (apply (accok_acc_sub RT AF Σs mm LVF (rt_frames RT Σ) pp 8 A ltac:(lia) SUBs
         ltac:(intros e He; repeat match goal with H : rt_frames RT _ = _ |- _ => rewrite H end; exact He) OWNc)) end.
    repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H in * end.
    unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
    refresh RT AF. unfold SHB in *. park_disj.
    walk_to AF MST [(usp - 96, usp); (pp, pp + 8)] (@nil Z).
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [| exact I]];
                        intros zz Hzz; unfold parked in OWN;
                        apply (aclient_mono LVF (rt_frames RT Σ) (usp + -96) _ _ _ zz (accok_aclient LVF (rt_frames RT Σ) m (usp + -96) pp 8 zz OWN ltac:(lia)));
                        [exact SUBs| intros e He; repeat match goal with H : rt_frames RT _ = _ |- _ => rewrite H end; exact He| lia]).
    lazymatch goal with
    | AGFx : agree_on ?PFx _ ?mm, MUx : munch _ ?mm _ |- _ =>
        is_var PFx; agf_munch AGFx MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct Hx as [_ Ho]; cbn [outside] in Ho; repeat split; first [lia| tauto])
    end.
    apply cps_finish; intros c Hc; subst QF; cbv beta. unfold hid in LVFIN.
    exists Σs. eexists.
    split; [| split; [exact LVFIN| split; [congruence| split; [congruence|]]]].
    2:{ repeat match goal with H : rt_credit RT _ = _ |- _ => rewrite H end. exact CRK. }
    eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-; eexists.
    split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
    split; [split; [split; [assumption| split; assumption]| split; assumption]|].
    split; [| assumption].
    intros a Ha Ho. apply AGFk. split; [| exact Ho]. rewrite LVFIN in Ha. exact Ha. }
  set (SL := fun e : Z * selv * list byte => sel_live (fst (fst e)) (snd (fst e))).
  set (dflt := (0, mkSelv 0 0 0 0 0 0 [], []) : Z * selv * list byte).
  assert (SLOTS0 : forall j, (j < length sels)%nat -> rw_cells asegs m (arr + 8 * (0 + Z.of_nat j)) [C8 (Z_to_bv 64 (fst (fst (nth j sels dflt))))]).
  { intros j Hj. pose proof SAO as (_ & _ & _ & _ & ARRC0 & _).
    replace (map (fun e : Z * selv * list byte => C8 (Z_to_bv 64 (fst (fst e)))) sels ++ repeat (C8 (Z_to_bv 64 0)) (50 - length sels))
      with (map C8 (map (fun e : Z * selv * list byte => Z_to_bv 64 (fst (fst e))) sels ++ repeat (Z_to_bv 64 0) (50 - length sels))) in ARRC0
      by (rewrite map_app, map_map, map_repeat; reflexivity).
    replace (0 + Z.of_nat j) with (Z.of_nat j) by lia.
    apply (C8s_slot m arr _ j _ ARRC0). rewrite nth_error_app1 by (rewrite length_map; exact Hj).
    rewrite nth_error_map. rewrite (nth_error_nth' sels dflt Hj). reflexivity. }
  lazymatch goal with FRx : rw_cells asegs _ (usp + -96) ?frcs |- _ =>
  assert (LOOP : forall (rem done : list (Z * selv * list byte)) (i c6 : Z) (Σk : rts RT) (mc : mem)
                 (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32),
     sels = done ++ rem -> rem <> [] -> i = Z.of_nat (length done) -> c6 = 8 * i ->
     hid (rt_live RT Σk = l1 ++ flat_map SL (rev rem) ++ [(arr, 400); (sela, 16)] ++ l2) -> List.NoDup (map fst (rt_live RT Σk)) ->
     (forall p k, In (p, k) (rt_live RT Σk) -> 0 < k) ->
     rt_frames RT Σk = rt_frames RT Σ -> rt_sp0 RT Σk = rt_sp0 RT Σ -> rt_credit RT Σ <= rt_credit RT Σk ->
     ART RT Σk mc -> mem_inv asegs mc -> stk asegs mc lo (usp + -96) -> LIBH mc -> io_ssp mc -> agree_on PF m mc ->
     rw_cells asegs mc (usp + -96) frcs ->
     rw_cells asegs mc sela [C4 (Z_to_bv 64 n); C4 (Z_to_bv 64 50); C8 (Z_to_bv 64 arr)] ->
     hid (rw_cells asegs mc pp [C8 (Z_to_bv 64 sela)]) ->
     Forall (fun e => sel_obj (rt_live RT Σk) mc (fst (fst e)) (snd (fst e)) (snd e)) rem ->
     (forall j, (j < length rem)%nat -> rw_cells asegs mc (arr + 8 * (i + Z.of_nat j)) [C8 (Z_to_bv 64 (fst (fst (nth j rem dflt))))]) ->
     cps asegs (ASTA RT Σk PMc (eq (MS (mkR ra' (Z_to_bv 64 (usp + -96)) gp (Z_to_bv 64 D_defs.TP_A) t0' t1' t2' (Z_to_bv 64 pp) (Z_to_bv 64 sela)
          a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (sela + 8)) (Z_to_bv 64 (pp / 8 + 2147450880)) (Z_to_bv 64 2147450880)
          (Z_to_bv 64 (sela / 8 + 2147450880)) (Z_to_bv 64 c6) (Z_to_bv 64 i) (Z_to_bv 64 ((sela + 8) / 8 + 2147450880))
          (Z_to_bv 64 (Z.land sela 7 + 3)) s10 s11 t3' t4' t5' t6') F' (Z_to_bv 64 0xa710c) fc' None mc (seg_rom asegs)))) QF) end.
  { clear AGF SLOTS0.
    repeat match goal with H : rw_cells asegs _ _ _ |- _ => clear H end.
    repeat match goal with H : ro_cells asegs _ _ _ |- _ => clear H end.
    repeat match goal with H : bytes_at asegs _ _ _ |- _ => clear H end.
    repeat match goal with H : munch _ _ _ |- _ => clear H end.
    repeat match goal with H : acc asegs _ _ _ |- _ => clear H end.
    repeat match goal with H : ART RT _ _ |- _ => lazymatch type of H with ART RT Σ m => fail | _ => clear H end end.
    repeat match goal with H : wmono asegs _ _ |- _ => clear H end.
    repeat match goal with H : mem_inv asegs _ |- _ => clear H end.
    repeat match goal with H : stk asegs _ _ _ |- _ => clear H end.
    repeat match goal with H : LIBH _ |- _ => clear H end.
    repeat match goal with H : io_ssp _ |- _ => clear H end.
    clear SAO SELS.
    induction rem as [|e rem' IH]; intros done i c6 Σk mc ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc'
      ESELS RNE -> -> LVK NDk POSk FRK SPK CRK ARTk MIk STk LHk SSPk AGFk FRc SAC PPC SOS SLOTS.
    { contradiction. }
    clear RNE. destruct e as [[sel v] nm].
    pose proof (Forall_inv SOS) as SO. pose proof (Forall_inv_tail SOS) as SOREM. cbn [fst snd] in SO. clear SOS.
    pose proof (SLOTS 0%nat ltac:(cbn [length]; lia)) as SLOT0. cbn [nth fst] in SLOT0. replace (Z.of_nat (length done) + Z.of_nat 0) with (Z.of_nat (length done)) in SLOT0 by lia.
    set (i := Z.of_nat (length done)) in *.
    assert (IBND : i + 1 + Z.of_nat (length rem') = n /\ 0 <= i) by (unfold n, i; rewrite ESELS, length_app; cbn [length]; lia).
    destruct IBND as (IBND & I0).
    assert (N50 : n <= 50) by (unfold n; lia).
    assert (SHAPE2 : rt_live RT Σk = (l1 ++ flat_map SL (rev rem')) ++ sel_live sel v ++ ([(arr, 400); (sela, 16)] ++ l2)).
    { unfold hid in LVK. rewrite LVK. cbn [rev]. rewrite flat_map_app. cbn [flat_map]. rewrite app_nil_r. unfold SL at 2. cbn [fst snd].
      rewrite <- !app_assoc. reflexivity. }
    assert (INAk : In (arr, 400) (rt_live RT Σk)) by (rewrite SHAPE2; apply in_or_app; right; apply in_or_app; right; left; reflexivity).
    assert (INSk : In (sela, 16) (rt_live RT Σk)) by (rewrite SHAPE2; apply in_or_app; right; apply in_or_app; right; right; left; reflexivity).
    hide SHAPE2.
    refresh RT AF. unfold SHB in *. park_disj.
    walk_to AF MST [(usp - 96, usp)] [e_selDestroy].
    hide SAC.
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
    assert (ARNF : ~ In arr (sel_frees sel v)).
    { intros Hf. apply sel_frees_live in Hf. unfold hid in SHAPE2. rewrite SHAPE2 in NDk. rewrite map_app in NDk. apply NoDup_app_remove_l in NDk.
      rewrite map_app in NDk. apply (nodup_app_disj _ _ _ arr NDk Hf). cbn [map fst app]. left. reflexivity. }
    eapply cps_seq.
    { eapply SDS with (lo := lo) (pp := arr + 8 * i) (sel := sel) (v := v) (nm := nm) (q := arr) (qn := 400)
                      (l1 := l1 ++ flat_map SL (rev rem')) (l2 := [(arr, 400); (sela, 16)] ++ l2); rt_side idtac.
      all: try lia.
      all: lazymatch goal with
           | |- lenv _ _ _ _ _ _ => lenv_tac
           | |- In _ (live_remove_all _ _) => apply live_remove_all_In; split; [exact INAk| exact ARNF]
           | |- sel_obj _ _ _ _ _ => exact SO
           | |- rt_live _ _ = _ => unfold hid in SHAPE2; exact SHAPE2
           | |- forall _ _, In _ _ -> _ => exact POSk
           | |- rw_cells _ _ _ _ => exact SLOT0
           | |- _ mod 8 = 0 => clear - AR16; Z.div_mod_to_equations; lia
           | |- _ => idtac
           end. }
    clear SLOT0.
    after_call RT AF.
    lazymatch goal with H : rt_live RT ?S = live_remove_all (sel_frees sel v) _ |- _ => rename H into LVN; rename S into Σn end.
    assert (NEWSHAPE : rt_live RT Σn = l1 ++ flat_map SL (rev rem') ++ [(arr, 400); (sela, 16)] ++ l2).
    { unfold hid in SHAPE2. rewrite LVN, SHAPE2. rewrite (app_assoc l1 (flat_map SL (rev rem')) ([(arr, 400); (sela, 16)] ++ l2)).
      apply live_remove_all_mid; [rewrite <- SHAPE2; exact NDk| intros p; apply sel_frees_live]. }
    assert (NDn : List.NoDup (map fst (rt_live RT Σn))) by (rewrite LVN; apply live_remove_all_nodup; exact NDk).
    assert (POSn : forall p k, In (p, k) (rt_live RT Σn) -> 0 < k) by (intros p k Hp; rewrite LVN in Hp; apply live_remove_all_In in Hp; exact (POSk p k (proj1 Hp))).
    assert (INAn : In (arr, 400) (rt_live RT Σn)) by (rewrite NEWSHAPE; apply in_or_app; right; apply in_or_app; right; left; reflexivity).
    assert (INSn : In (sela, 16) (rt_live RT Σn)) by (rewrite NEWSHAPE; apply in_or_app; right; apply in_or_app; right; right; left; reflexivity).
    assert (SUBn : forall e, In e LVF -> In e (rt_live RT Σn)).
    { intros e He. rewrite LVFEQ in He. rewrite NEWSHAPE. apply in_app_or in He. apply in_or_app. destruct He as [He|He]; [left; exact He| right; apply in_or_app; right; right; right; exact He]. }
    pose proof (PPAP arr 400 ARIN ARFR) as PPARR.
    lazymatch goal with AG : agree_on ?P2 mc ?m1, ARTn : ART RT Σn ?m1 |- _ =>
      (* [comment removed for export] *)
      unfold hid in SAC;
      apply (rw_cells_agree_nw asegs mc m1 sela _) in SAC;
        [| eapply agree_sub; [exact AG|]; intros zz Hzz; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Hzz;
           split; [right; right; left; exists sela, 16; split; [exact INSn| lia]| cbn [outside]; unfold parked in QSA; clear - Hzz QSA I0 IBND N50; split; [lia| exact I]]];
      (* [comment removed for export] *)
      unfold hid in PPC;
      apply (rw_cells_agree_nw asegs mc m1 pp _) in PPC;
        [| eapply agree_sub; [exact AG|]; intros zz Hzz; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Hzz;
           split; [unfold parked in OWN; apply (aclient_mono LVF (rt_frames RT Σ) (usp + -96) _ _ (usp + -96) zz (accok_aclient LVF (rt_frames RT Σ) m (usp + -96) pp 8 zz OWN ltac:(lia)));
                   [exact SUBn| intros e He; repeat match goal with H : rt_frames RT _ = _ |- _ => rewrite H end; exact He| lia]
                  | cbn [outside]; clear - Hzz PPARR I0 IBND N50; split; [lia| exact I]]];
      (* [comment removed for export] *)
      assert (SOREMn : Forall (fun e => sel_obj (rt_live RT Σn) m1 (fst (fst e)) (snd (fst e)) (snd e)) rem');
        [ apply Forall_forall; intros e' He'; pose proof (proj1 (Forall_forall _ _) SOREM e' He') as SO'; cbv beta in SO';
          assert (INC : forall c, In c (SL e') -> In c (rt_live RT Σn))
            by (intros c Hc; rewrite NEWSHAPE; apply in_or_app; right; apply in_or_app; left; apply in_flat_map; exists e'; split; [apply -> in_rev; exact He'| exact Hc]);
          apply (sel_obj_agree2 (rt_live RT Σk) (rt_live RT Σn) mc m1 _ _ _ SO' INC);
          eapply agree_sub; [exact AG|]; intros zz (pz & kz & Hpz & Hzz);
          split; [right; right; left; exists pz, kz; split; [exact (INC _ Hpz)| exact Hzz]|];
          pose proof (live_segs_disj RT AF Σn m1 l1 (flat_map SL (rev rem')) [(arr, 400); (sela, 16)] l2 ARTn NEWSHAPE pz kz arr 400
                        ltac:(apply in_flat_map; exists e'; split; [apply -> in_rev; exact He'| exact Hpz]) ltac:(left; reflexivity)) as DJ;
          cbn [outside]; clear - Hzz DJ I0 IBND N50; split; [lia| exact I]
        |];
      (* [comment removed for export] *)
      assert (SLOTSn : forall j, (j < length rem')%nat -> rw_cells asegs m1 (arr + 8 * ((i + 1) + Z.of_nat j)) [C8 (Z_to_bv 64 (fst (fst (nth j rem' dflt))))]);
        [ intros j Hj; pose proof (SLOTS (S j) ltac:(cbn [length]; lia)) as SJ; cbn [nth] in SJ;
          replace (i + Z.of_nat (S j)) with (i + 1 + Z.of_nat j) in SJ by lia;
          apply (rw_cells_agree_nw asegs mc m1 _ _ SJ); eapply agree_sub; [exact AG|]; intros zz Hzz;
          cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Hzz;
          split; [right; right; left; exists arr, 400; split; [exact INAn| clear - Hzz Hj I0 IBND N50; lia]| cbn [outside]; clear - Hzz; split; [lia| exact I]]
        |]
    end.
    agf_call AGFk AG ltac:(fun Hx => pose proof (APARR _ Hx); destruct Hx as [Hx _]; split;
                            [apply (aclient_mono LVF _ usp _ _ _ _ Hx); [exact SUBn| intros e He; repeat match goal with H : rt_frames RT _ = _ |- _ => rewrite H end; exact He| lia]
                            | cbn [outside]; split; [lia| exact I]]).
    clear AG SO SOREM SLOTS INAk INSk.
    hide LVN. hide NEWSHAPE. hide PPC.
    repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H in * end.
    unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
    refresh RT AF. unfold SHB in *. park_disj.
    walk_to AF MST [(usp - 96, usp); (pp, pp + 8)] [0xa7124].
    lstep. shbr8_zero.
    sx32_fix.
    awalk [0xa7134].
    sx32_fix.
    destruct rem' as [|e2 rem''].
    - (* [comment removed for export] *)
      cbn [length] in IBND.
      lstep. brF.
      awalk [0xa7148].
      cps_stop.
      art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [| exact I]];
                          intros zz Hzz; unfold parked in OWN;
                          apply (aclient_mono LVF (rt_frames RT Σ) (usp + -96) _ _ _ zz (accok_aclient LVF (rt_frames RT Σ) m (usp + -96) pp 8 zz OWN ltac:(lia)));
                          [exact SUBn| intros e He; repeat match goal with H : rt_frames RT _ = _ |- _ => rewrite H end; exact He| lia]).
      lazymatch goal with
      | AGFx : agree_on ?PFx _ ?mm, MUx : munch _ ?mm _ |- _ =>
          is_var PFx; agf_munch AGFx MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct Hx as [_ Ho]; cbn [outside] in Ho; repeat split; first [lia| tauto])
      end.
      eapply TAIL; try eassumption.
      + congruence.
      + lazymatch goal with H : rt_credit RT Σk <= rt_credit RT Σn |- _ => clear - H CRK; lia end.
    - (* [comment removed for export] *)
      cbn [length] in IBND.
      lstep. brT.
      cps_stop.
      art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [| exact I]];
                          intros zz Hzz; unfold parked in OWN;
                          apply (aclient_mono LVF (rt_frames RT Σ) (usp + -96) _ _ _ zz (accok_aclient LVF (rt_frames RT Σ) m (usp + -96) pp 8 zz OWN ltac:(lia)));
                          [exact SUBn| intros e He; repeat match goal with H : rt_frames RT _ = _ |- _ => rewrite H end; exact He| lia]).
      lazymatch goal with
      | AGFx : agree_on ?PFx _ ?mm, MUx : munch _ ?mm _ |- _ =>
          is_var PFx; agf_munch AGFx MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct Hx as [_ Ho]; cbn [outside] in Ho; repeat split; first [lia| tauto])
      end.
      eapply (IH (done ++ [(sel, v, nm)]) (i + 1)); try eassumption.
      + rewrite ESELS, <- app_assoc. reflexivity.
      + discriminate.
      + rewrite length_app. cbn [length]. unfold i. lia.
      + lia.
      + congruence.
      + lazymatch goal with H : rt_credit RT Σk <= rt_credit RT Σn |- _ => clear - H CRK; lia end. }
  (* [comment removed for export] *)
  sx32_fix.
  destruct sels as [|e0 sels'].
  - brT.
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I]).
    lazymatch goal with
    | AGFx : agree_on ?PFx _ ?mm, MUx : munch _ ?mm _ |- _ =>
        is_var PFx; agf_munch AGFx MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I])
    end.
    hide PPC.
    eapply TAIL; try eassumption.
    + reflexivity.
    + reflexivity.
    + lia.
  - assert (NPOS : 0 < n <= 50) by (unfold n; cbn [length] in *; lia).
    brF.
    awalk [0xa710c].
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I]).
    lazymatch goal with
    | AGFx : agree_on ?PFx _ ?mm, MUx : munch _ ?mm _ |- _ =>
        is_var PFx; agf_munch AGFx MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I])
    end.
    hide PPC.
    eapply (LOOP (e0 :: sels') [] 0 0); try eassumption.
    + reflexivity.
    + discriminate.
    + reflexivity.
    + reflexivity.
    + unfold hid in *. rewrite SHAPE. unfold sela_live. rewrite <- app_assoc. reflexivity.
    + reflexivity.
    + reflexivity.
    + lia.
    + lazymatch goal with MUx : munch ?W m ?mc |- Forall _ _ =>
        apply Forall_forall; intros e He; pose proof (proj1 (Forall_forall _ _) SELS e He) as SO; cbv beta in SO;
        assert (INC : forall c, In c (SL e) -> In c (rt_live RT Σ))
          by (intros c Hc; unfold hid in SHAPE; rewrite SHAPE; apply in_or_app; right; apply in_or_app; left; unfold sela_live; apply in_or_app; left;
              apply in_flat_map; exists e; split; [apply -> in_rev; exact He| exact Hc]);
        apply (sel_obj_agree2 (rt_live RT Σ) (rt_live RT Σ) m mc _ _ _ SO INC);
        apply (agree_of_munch W m mc _ MUx); intros zz (pz & kz & Hpz & Hzz);
        pose proof (af_live_range RT AF Σ m pz kz ART0 (INC _ Hpz)) as (_ & RHI & _); unfold STACK_WIN in RHI;
        cbn [outside]; clear - Hzz RHI LOW LOR; split; [lia| exact I] end.
    + lazymatch goal with MUx : munch ?W m ?mc |- forall _, _ =>
        intros j Hj; apply (rw_cells_agree_nw asegs m mc _ _ (SLOTS0 j Hj)); apply (agree_of_munch W m mc _ MUx); intros zz Hzz;
        cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Hzz; cbn [length] in Hj;
        lazymatch goal with H : arr + 400 <= rt_sp0 RT Σ - 8388608 |- _ => cbn [outside]; clear - Hzz H Hj LOW LOR NPOS; unfold n in NPOS; cbn [length] in NPOS; split; [lia| exact I] end end.
Qed.
End SELAD.
