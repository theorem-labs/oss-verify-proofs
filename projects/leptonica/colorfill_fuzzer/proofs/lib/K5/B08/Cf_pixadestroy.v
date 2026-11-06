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
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.B08 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit Lept_chain Lept_leaf Lept_objkit Cf_iface Cf_kit CfX_kit LeptB_guard.
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

Section PIXAD.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis BDE : boxaDestroy_empty_cps RT.

Lemma tr_pd1 : In [0x8ea8c] CLIENT_TRACES.  Proof. vm_compute. tauto. Qed.
Lemma tr_pd2 : In [0x8ea9c] CLIENT_TRACES.  Proof. vm_compute. tauto. Qed.

Theorem pixaDestroy_ok : pixaDestroy_cps RT.
Proof using AF GP BDE.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pp pa nalloc parr ba barr
    FDO MST -> -> OP PPC CO ENV LVPOS.
  unfold pixa_obj, boxa_empty in CO.
  pose proof (gp_free RT GP) as FREE.
  unfold lpost_f, lenv, keeps, keepsL, optrL in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct OP as (OWN & PP0 & PP8 & PPH & PPS).
  destruct CO as ((ppad & PAC) & (INP & PA0 & PA16 & _) & (INR & PR0 & PR16 & PRN) & ((bpad & BAC) & (INB & BA0 & BA16 & _) & (INBR & BR0 & BR16 & BRN) & _ & _) & NAR & ND).
  pose_neqs ND. clear ND.
  set (LVF := live_remove pa (live_remove ba (live_remove barr (live_remove parr (rt_live RT Σ))))) in *.
  assert (LVFS : forall e, In e LVF -> In e (rt_live RT Σ))
    by (intros e He; unfold LVF in He; repeat apply live_remove_sub in He; exact He).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  assert (PPLO : pp + 8 <= lo).
  { destruct OWN as [(p & k & Hin & Q1 & Q2)|(f & k & Hin & Q1 & Q2 & _)].
    - pose proof (af_live_range RT AF Σ m p k ART0 (LVFS _ Hin)) as (_ & R & _). lia.
    - pose proof (af_frames_range RT AF Σ m f k ART0 Hin) as (_ & R & _). lia. }
  unfold entry_st, e_pixaDestroy, pixa_cells, boxa_cells in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold LSTK, STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  set (PF := fun a => aclient LVF (rt_frames RT Σ) usp a /\ outside [(pp, pp + 8)] a).
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a [Ha _]. destruct (aclient_split RT AF Σ m usp a ART0) as [HH|HH]; [| left; exact HH| right; unfold STACK_WIN in HH; lia].
    apply (aclient_mono LVF (rt_frames RT Σ) usp _ _ usp a Ha); [exact LVFS| auto| lia]. }
  assert (SUBP : forall e, In e LVF -> In e (rt_live RT Σ) /\ fst e <> pa)
    by (intros e He; split; [exact (LVFS _ He)| exact (proj2 (live_remove_in _ _ _ He))]).
  assert (SPW : rt_sp0 RT Σ - STACK_WIN <= usp) by (unfold STACK_WIN; clear - LOW LOR; lia).
  assert (PA_AP : forall a, PF a -> a < pa \/ pa + 32 <= a)
    by (intros a [Ha _]; exact (removed_chunk_apart RT AF Σ m pa 32 LVF usp a ART0 INP SUBP SPW Ha)).
  (* [comment removed for export] *)
  assert (PPPA : pp + 8 <= pa \/ pa + 32 <= pp).
  { pose proof (removed_chunk_apart RT AF Σ m pa 32 LVF usp pp ART0 INP SUBP SPW (accok_aclient _ _ _ usp pp 8 pp OWN ltac:(clear; lia))) as E1.
    pose proof (removed_chunk_apart RT AF Σ m pa 32 LVF usp (pp + 7) ART0 INP SUBP SPW (accok_aclient _ _ _ usp pp 8 (pp + 7) OWN ltac:(clear; lia))) as E2.
    clear - E1 E2. lia. }
  pose proof (live_apart RT AF Σ m pa 32 ba 24 ART0 INP INB ltac:(assumption)) as D_PB.
  clear SUBP SPW.
  chunk_facts RT AF GP pa 32. chunk_facts RT AF GP ba 24.
  split_at PAC 5%nat PAB.
  refresh RT AF.
  cps_walk AF MST.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 96, usp); (pa + 8, pa + 12)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  carve_frame 96%nat ST.
  Time awalk [0x5ede4; 0x8efb8].
  assert (AMO : amo_aligned AW (Z_to_bv 64 (pa + 8)) = true) by (apply cfx_amo_aligned; [clear - PA0 CKR SP0R; lia| clear - PA16; Z.div_mod_to_equations; lia]).
  cfx_amo_sub1 AMO 1 ltac:(clear; lia).
  rewrite ?(sx32_small 1) by (clear; lia). try br.
  Time awalk [0x5ede4; 0x8efb8].
  cps_stop.
  art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists pa, 32; split; [exact INP| lia]| exact I]]).
  to_entry.
  agf_munch AGF MU ltac:(fun Hx => cbn [outside]; pose proof (PA_AP _ Hx) as HxA; pose proof (PFS _ Hx) as HxS; split; [clear - HxS LOW LOR; lia| split; [clear - HxA; lia| exact I]]).
  eapply cps_seq.
  { eapply FREE with (lo := lo) (p := parr) (n := 8 * nalloc); try reflexivity; try assumption.
    - unfold call_ok. rewrite unsigned_lit by ul. split; [eassumption| ul].
    - apply unwind_okC_of_ok; rewrite !unsigned_lit by ul; [exact tr_pd1| left; ul]. }
  Time after_call RT AF.
  fold_ag ltac:(fun Hx => destruct Hx as [Hx _]; apply (aclient_mono LVF (rt_frames RT Σ) usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]).
  refresh RT AF.
  cps_walk AF MST.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(usp - 96, usp)] mm) as MU1; pose proof (wmono_refl asegs mm) as WM1 end.
  Time awalk [0x5ede4; 0x8efb8].
  cps_stop. to_entry.
  agf_munch AGF MU1 ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx) as HxS; split; [clear - HxS LOW LOR; lia| exact I]).
  pose proof BDE as BC. unfold boxaDestroy_empty_cps in BC.
  eapply cps_seq.
  { eapply BC with (lo := lo) (pp := pa + 24) (ba := ba) (nalloc := nalloc) (arr := barr); rt_side idtac.
    all: lazymatch goal with
         | |- optrL _ _ _ _ _ _ => unfold optrL; split; [left; exists pa, 32; split; [solve [in_live_tac]| clear; lia]|];
                                   unfold SEGTOP_A; clear - PA0 PA16 CKS CKH; repeat split; first [lia | Z.div_mod_to_equations; lia]
         | |- rw_cells _ _ _ [C8 _] => exact PAB
         | |- boxa_empty _ _ _ _ _ => unfold boxa_empty, chunk, boxa_cells; split; [exists bpad; exact BAC|];
                                      repeat split; first [solve [in_live_tac] | assumption | lia]
         | |- lenv _ _ _ _ _ _ => lenv_tac
         | |- forall p n, In (p, n) _ -> 0 < n => lvp_tac LVPOS
         | |- ?g => idtac "LEFT:" g
         end. }
  Time after_call RT AF.
  fold_ag ltac:(fun Hx => pose proof (PA_AP _ Hx) as HxA; destruct Hx as [Hx _]; split;
                  [apply (aclient_mono LVF (rt_frames RT Σ) usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| clear; lia]
                  | cbn [outside]; split; [clear - HxA; lia| exact I]]).
  refresh RT AF.
  cps_walk AF MST.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(usp - 96, usp)] mm) as MU2; pose proof (wmono_refl asegs mm) as WM2 end.
  Time awalk [0x5ede4; 0x8efb8].
  cps_stop. to_entry.
  agf_munch AGF MU2 ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx) as HxS; split; [clear - HxS LOW LOR; lia| exact I]).
  eapply cps_seq.
  { eapply FREE with (lo := lo) (p := pa) (n := 32); try reflexivity; try assumption.
    - solve [in_live_tac].
    - unfold call_ok. rewrite unsigned_lit by ul. split; [eassumption| ul].
    - apply unwind_okC_of_ok; rewrite !unsigned_lit by ul; [exact tr_pd2| left; ul]. }
  Time after_call RT AF.
  fold_ag ltac:(fun Hx => destruct Hx as [Hx _]; apply (aclient_mono LVF (rt_frames RT Σ) usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]).
  refresh RT AF.
  cps_walk AF MST.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(usp - 96, usp); (pp, pp + 8)] mm) as MU4; pose proof (wmono_refl asegs mm) as WM4 end.
  Time awalk0.
  cps_stop.
  agf_munch AGF MU4 ltac:(fun Hx => cbn [outside]; destruct Hx as [Hx1 Hx2]; cbn [outside] in Hx2; pose proof (PFS _ (conj Hx1 Hx2)) as HxS;
                                    split; [clear - HxS LOW LOR PPLO; lia| split; [clear - Hx2; tauto| exact I]]).
  apply cps_finish. intros c Hc. subst QF. cbv beta.
  lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S end.
  eexists. split.
  - eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-. eexists. split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
    split; [split; [split; [| split; [assumption| assumption]]| split; assumption]|].
    + lazymatch goal with A : ART RT ?S ?mm, MUx : munch ?W ?mm ?mf, WMx : wmono asegs ?mm ?mf |- ART RT ?S ?mf =>
        apply (art_client_writes RT AF S mm mf (usp + -96) W A MUx WMx) end.
      * repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end. ul.
      * cbn [ivls_client]. split; [intros zz Hzz; left; ul|]. split; [| exact I]. intros zz Hzz.
        lazymatch goal with |- aclient ?lv' ?frs' ?sp' _ => 
          apply (aclient_mono LVF (rt_frames RT Σ) sp' lv' frs' sp' zz); [exact (accok_aclient _ _ _ sp' pp 8 zz OWN Hzz)| solve [live_sub_tac]| solve [frames_sub_tac]| lia] end.
    + split; [| assumption]. intros a Ha Ho. apply AGF. split; [| exact Ho].
      lazymatch type of Ha with aclient ?lv _ _ _ => replace lv with LVF in Ha; [exact Ha|] end.
      repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end. reflexivity.
  - repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end.
    repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end.
    repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end.
    repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end. repeat split; auto; lia.
Qed.

Theorem pixaDestroy_null_ok : pixaDestroy_null_cps RT.
Proof using AF GP.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pp
    FDO MST -> -> OP PPC ENV.
  unfold lpost, lenv, keeps, keepsL, optr, optrL in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct OP as (OWN & PP0 & PP8 & PPH & PPS).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  assert (PPLO : pp + 8 <= lo).
  { destruct OWN as [(p & k & Hin & Q1 & Q2)|(f & k & Hin & Q1 & Q2 & _)].
    - pose proof (af_live_range RT AF Σ m p k ART0 Hin) as (_ & R & _). lia.
    - pose proof (af_frames_range RT AF Σ m f k ART0 Hin) as (_ & R & _). lia. }
  unfold entry_st, e_pixaDestroy in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold LSTK, STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  set (PF := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a).
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a Ha. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [HH|HH]; [left; exact HH| right; unfold STACK_WIN in HH; lia]. }
  pose proof ST as (STa & STb & _).
  refresh RT AF.
  cps_walk AF MST.
  pose proof (munch_refl [(usp - 96, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  carve_frame 96%nat ST.
  Time awalk0.
  cps_stop.
  art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I]).
  agf_munch AGF MU ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx) as HxS; split; [clear - HxS LOW LOR; lia| exact I]).
  apply cps_finish. intros c Hc. subst QF. cbv beta.
  exists Σ. eexists. split; [| repeat split; reflexivity].
  eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-. eexists. split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
  split; [split; [split; [assumption| split; [assumption| split; [assumption| assumption]]]| split; assumption]|].
  intros a Ha _. exact (AGF a Ha).
Qed.
End PIXAD.
