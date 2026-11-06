(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.A9 Require Import ImageA.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Malloc Require Import MallocKit_AB.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.A9 Require Import Layout.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.A9 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit Lept_chain Lept_objkit LeptL_kit Lept_fuzzkit LeptM_destroy_defs Ed_fp Ed_iface Numa_kit Ed_tracekit.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section NUMAD.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.

Theorem numaDestroy_ok : numaDestroy_cps RT.
Proof using AF GP.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pna na cap arr vals
    FDO MST -> -> OP PCC OB ENV RES.
  pose proof (gp_free RT GP) as FREE.
  unfold lpost_f, lenv, lres, keeps, keepsL, optrF in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct OP as (OWN & PC0 & PC8 & PCH & PCS).
  pose proof (numa_obj_facts _ _ _ _ _ _ OB) as (LEN & CAP & NA0 & NA16 & AR0 & AR16 & INn & INa & NE).
  destruct OB as ((pad & NC) & _ & _). unfold numa_cells in NC.   (* [comment removed for export] *)
  pose proof (af_client_consts RT AF Σ m ART0) as (G1 & G2 & _).
  assert (ACCP : acc asegs m pna 8).
  { apply (accok_acc RT AF Σ m pna 8 ART0 ltac:(lia)). right. exact OWN. }
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  assert (PCLO : pna + 8 <= lo).
  { destruct OWN as (f & k & Hin & H1 & H2 & _). pose proof (af_frames_range RT AF Σ m f k ART0 Hin) as (_ & R & _). lia. }
  pose proof (af_acc_live RT AF Σ m na 32 ART0 INn) as (WRN & ACCN).
  pose proof (af_live_range RT AF Σ m na 32 ART0 INn) as (_ & NAR & NAS).
  pose proof (gp_live_hi RT GP Σ m na 32 ART0 INn) as NASH.
  pose proof (af_live_range RT AF Σ m arr (4 * cap) ART0 INa) as (_ & ARR & ARS).
  assert (DJ : na + 32 <= arr \/ arr + 4 * cap <= na).
  { destruct (In_split _ _ INn) as (l1 & l2 & E).
    assert (INa' : In (arr, 4 * cap) (l1 ++ l2)).
    { rewrite E in INa. apply in_app_iff in INa. apply in_app_iff. destruct INa as [H|[H|H]]; [left; exact H| injection H; lia| right; exact H]. }
    pose proof (af_live_disj RT AF Σ m na 32 arr (4 * cap) l1 l2 ART0 E INa') as X. lia. }
  (* [comment removed for export] *)
  assert (PNA : pna + 8 <= na \/ na + 32 <= pna).
  { destruct OWN as (f & k & Hin & H1 & H2 & _). pose proof (af_frames_range RT AF Σ m f k ART0 Hin) as (_ & _ & _ & R). pose proof (R na 32 INn). lia. }
  assert (PAR : pna + 8 <= arr \/ arr + 4 * cap <= pna).
  { destruct OWN as (f & k & Hin & H1 & H2 & _). pose proof (af_frames_range RT AF Σ m f k ART0 Hin) as (_ & _ & _ & R). pose proof (R arr (4 * cap) INa). lia. }
  unfold entry_st, e_numaDestroy, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold LSTK, STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  set (LVF := live_remove na (live_remove arr (rt_live RT Σ))) in *.
  set (PF := fun a => aclient LVF (rt_frames RT Σ) usp a /\ outside [(pna, pna + 8)] a).
  assert (OWNA : accok LVF (rt_frames RT Σ) m pna 8) by (right; exact OWN).   (* [comment removed for export] *)
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a [Ha _]. destruct (aclient_split RT AF Σ m usp a ART0) as [H|H]; [| left; exact H| right; unfold STACK_WIN in H; lia].
    apply (aclient_mono LVF (rt_frames RT Σ) usp _ _ usp a Ha); [| auto| lia].
    intros e He. exact (live_remove_sub _ _ _ (live_remove_sub _ _ _ He)). }
  assert (NAP : forall a, PF a -> a < na \/ na + 32 <= a).
  { intros a [Ha _]. apply (removed_chunk_apart RT AF Σ m na 32 LVF usp a ART0 INn); [| unfold STACK_WIN; lia| exact Ha].
    intros e He. unfold LVF in He. destruct (live_remove_in _ _ _ He) as [He1 NE1]. split; [exact (live_remove_sub _ _ _ He1)| exact NE1]. }
  cps_walk AF MST.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 32, usp); (na + 8, na + 12)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  carve_frame 32%nat ST.
  awalk [0xeee20; 0xb85e0; 0xeee6c; 0xeeeb8].          (* [comment removed for export] *)
  assert (AMO : amo_aligned AW (Z_to_bv 64 (na + 8)) = true).
  { unfold amo_aligned, amo_bytes. rewrite unsigned_lit by lia. apply Z.eqb_eq. clear - NA16 NA0. Z.div_mod_to_equations; lia. }
  amo_step AMO.
  awalk [0xb85e0; 0xeee5c; 0xeeeb8].                   (* [comment removed for export] *)
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [| exact I]];
                      intros zz Hzz; right; right; left; exists na, 32; split; [exact INn| lia])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); pose proof (NAP _ Hx); destruct Hx as [Hx1 Hx2]; cbn [outside] in Hx2;
                      repeat split; try exact I; lia).
  eapply cps_seq.
  { eapply FREE with (lo := lo); try reflexivity; try eassumption.
    all: first [ solve [in_live_tac]
               | unfold call_ok; rewrite unsigned_lit by ul; split; [eassumption| ul]
               | apply unwind_okC_of_ok; rewrite !unsigned_lit by ul; [exact tr_numaDestroy_1| left; ul] ]. }
  after_call RT AF.
  agf_call AGF AG ltac:(fun Hx => destruct Hx as [Hx _]; apply (aclient_mono LVF (rt_frames RT Σ) usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]).
  refresh RT AF.
  cps_walk AF MST.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(usp - 32, usp)] mm) as MU1; pose proof (wmono_refl asegs mm) as WM1 end.
  awalk [0xb85e0; 0xeeeb8].
  cps_stop. to_entry.
  agf_munch AGF MU1 ltac:(fun Hx => cbn [outside]; split; [destruct (PFS _ Hx); lia| exact I]).
  eapply cps_seq.
  { eapply FREE with (lo := lo); try reflexivity; try eassumption.
    all: first [ solve [in_live_tac]
               | unfold call_ok; rewrite unsigned_lit by ul; split; [eassumption| ul]
               | apply unwind_okC_of_ok; rewrite !unsigned_lit by ul; [exact tr_numaDestroy_2| left; ul] ]. }
  after_call RT AF.
  agf_call AGF AG0 ltac:(fun Hx => destruct Hx as [Hx _]; apply (aclient_mono LVF (rt_frames RT Σ) usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]).
  refresh RT AF.
  cps_walk AF MST.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(usp - 32, usp); (pna, pna + 8)] mm) as MU2; pose proof (wmono_refl asegs mm) as WM2 end.
  awalk0.
  cps_stop.
  agf_munch AGF MU2 ltac:(fun Hx => cbn [outside]; destruct Hx as [Hx1 Hx2]; cbn [outside] in Hx2; split; [destruct (PFS _ (conj Hx1 Hx2)); lia| split; [tauto| exact I]]).
  apply cps_finish. intros c Hc. subst QF. cbv beta.
  lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S end.
  eexists. split.
  - eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-. eexists. split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
    split; [split; [split; [| split; [assumption| assumption]]| split; assumption]|].
    + lazymatch goal with A : ART RT ?S ?mm, MUx : munch ?W ?mm ?mf, WMx : wmono asegs ?mm ?mf |- ART RT ?S ?mf =>
        apply (art_client_writes RT AF S mm mf (usp + -32) W A MUx WMx) end.
      * repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end. ul.
      * cbn [ivls_client]. split; [intros zz Hzz; left; ul|]. split; [| exact I]. intros zz Hzz.
        lazymatch goal with |- aclient ?lv' ?frs' ?sp' _ =>
          apply (aclient_mono LVF (rt_frames RT Σ) sp' lv' frs' sp' zz); [exact (accok_aclient _ _ _ sp' pna 8 zz OWNA Hzz)| solve [live_sub_tac]| solve [frames_sub_tac]| lia] end.
    + split; [| assumption]. intros a Ha Ho. apply AGF. split; [| exact Ho].
      lazymatch type of Ha with aclient ?lv _ _ _ => replace lv with LVF in Ha; [exact Ha|] end.
      unfold LVF, numa_gone. repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end. reflexivity.
  - unfold numa_gone. repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end.
    repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end.
    repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end.
    repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end. repeat split; auto; lia.
Qed.
End NUMAD.
