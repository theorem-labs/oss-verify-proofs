(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.B9 Require Import ImageA.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr FP.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.B9 Require Import Layout.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.B9 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit D_iface D_defs Lept_kit Lept_iface Lept_env LeptC_kit Lept_chain Lept_leaf Lept_objkit LeptL_kit Lept_fuzzkit Lept_gmax_defs Ed_fp Ed_iface Ed_fpkit Numa_kit Ed_tracekit Ed_numa_leaf Ed_ext_defs.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* [comment removed for export] *)
Local Ltac seg_side NAR ARR LOW LOR FRHI FR0 SP0W FRSEG FR64 FCD FCD0 FCD1 FCD2 FSA Hx :=
  repeat match goal with H : rt_sp0 _ _ = rt_sp0 _ _ |- _ => rewrite H in Hx end;
  cbn [outside]; unfold parked, shad, SHB, STACK_WIN, SEGTOP_A in *; clear - Hx NAR ARR LOW LOR FRHI FR0 SP0W FRSEG FR64 FCD FCD0 FCD1 FCD2 FSA;
  repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia].

(* [comment removed for export] *)
Local Ltac leaf_side NASH NAS FCD FCS FCD0 FCS0 FRSH FR64 LOR LOW SP0W SPB SP0Rb NAR ARR FRHI FR0 FRSEG :=
  first [ assumption
        | lazymatch goal with
          | |- _ \/ _ => clear - NASH NAS FCD FCS FCD0 FCS0 FRSH; unfold parked, SEGTOP_A, SHB in *; lia
          | |- _ mod _ = 0 => clear - FR64; Z.div_mod_to_equations; lia
          | |- _ => clear - LOR LOW SP0W SPB SP0Rb NAR ARR FRHI FR0 FRSEG; unfold parked, SEGTOP_A, STACK_WIN, USTACK_TOP in *; lia
          end ].

(* [comment removed for export] *)
Local Ltac lres_tac9 LVP :=
  unfold lres; repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end;
  repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end;
  unfold numa_live; cbn [length]; unfold FRAMES_MAX, LIVE_MAX in *;
  repeat lazymatch goal with |- _ /\ _ => split end;
  [ lia | lia | lia
  | let p := fresh "p" in let n := fresh "n" in let H := fresh "H" in intros p n H; cbn [In] in H;
    repeat (destruct H as [H|H]; [injection H; intros; subst; lia|]); exact (LVP p n H) ].

(* [comment removed for export] *)
Local Ltac obj_fwd NOBJ MU apart :=
  lazymatch type of MU with munch ?W ?ma ?mb =>
  lazymatch type of NOBJ with numa_obj ?lv ma ?na ?c ?ar ?vs =>
    apply (numa_obj_keep lv ma mb na c ar vs) in NOBJ;
    [| apply (keeps_live_of_munch lv W ma mb MU);
       let b := fresh "b" in let k := fresh "k" in let a := fresh "a" in let Hin := fresh "Hin" in let Ha := fresh "Ha" in
       intros b k a Hin Ha; apart b k a Hin Ha ]
  end end.
(* [comment removed for export] *)
Local Ltac obj_fwd_ag NOBJ AG inP :=
  lazymatch type of AG with agree_on ?P ?ma ?mb =>
  lazymatch type of NOBJ with numa_obj ?lv ma ?na ?c ?ar ?vs =>
    apply (numa_obj_keep lv ma mb na c ar vs) in NOBJ;
    [| apply (keeps_live_of_agree lv P ma mb AG);
       let b := fresh "b" in let k := fresh "k" in let a := fresh "a" in let Hin := fresh "Hin" in let Ha := fresh "Ha" in
       intros b k a Hin Ha; inP b k a Hin Ha ]
  end end.

Section EXTPRE.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis EG : ed_gaps RT.
Hypothesis NCR : numaCreate_cps RT.
Hypothesis EXT_REST : ext_rest_stmt RT.

Lemma ext_pre_c16 : ext_case RT 16.
Proof using AF GP EG NCR EXT_REST.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo nas cap arr vals ras
    FDO MST -> -> FV -> OB VLEN UC TR ENV RES AL.
  lazymatch goal with |- cps _ _ ?Q => change Q with (ext_post RT Σ PMc ra sp gp (Z_to_bv 64 TP_A) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo vals) end.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  unfold lpost_f, lenv, lres, keeps, keepsL, freg_is in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct RES as (FRB & LVB & CRB & LVP). unfold uctx in UC.
  pose proof (numa_obj_facts _ _ _ _ _ _ OB) as (LEN & CAP & NA0 & NA16 & AR0 & AR16 & INn & INa & NE). destruct CAP as [CAPa CAPb].
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF Σ m ART0) as (SP0Ra & SP0Rb). pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  pose proof (af_live_range RT AF Σ m nas 32 ART0 INn) as (_ & NAR & NAS).
  pose proof (gp_live_hi RT GP Σ m nas 32 ART0 INn) as NASH.
  pose proof (af_live_range RT AF Σ m arr (4 * cap) ART0 INa) as (_ & ARR & ARS).
  pose proof (gp_live_hi RT GP Σ m arr (4 * cap) ART0 INa) as ARSH.
  pose proof (live_apart RT AF Σ m nas 32 arr (4 * cap) ART0 INn INa ltac:(congruence)) as DJ.
  unfold entry_st, e_numaFindExtrema, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range). destruct USP as [USPa USPb].
  unfold LSTK, STDERR_STACK in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  pose proof EGC_val as EGC. unfold EXTREMA_COST in *.
  pose proof ST as (STa & STb & _).
  set (PF := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a /\ outside (@nil (Z * Z)) a).
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a [Ha _]. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]. }
  pose proof OB as NOBJ. clear OB.   (* [comment removed for export] *)
  carve_frame 208%nat ST.
  walk_to AF MST [(usp + -208, usp)] [e_stack_malloc 0%nat].
  (* [comment removed for export] *)
  repeat match goal with |- context [reg_get F ?r] => replace (reg_get F r) with DELTA_W by (symmetry; exact FV) end.
  rewrite delta_rebox.
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
  lazymatch goal with MUx : munch _ m ?m1 |- _ =>
    obj_fwd NOBJ MUx ltac:(fun b k a Hin Ha => pose proof (af_live_range RT AF Σ m b k ART0 Hin) as (_ & R & _); cbn [outside]; clear - R Ha LOW LOR;
                           unfold STACK_WIN, SEGTOP_A in *; repeat split; try exact I; lia) end.
  (* [comment removed for export] *)
  eapply cps_seq.
  { pose proof (eg_stack_malloc0F RT EG) as SM0; unfold stack_malloc_contractF in SM0; eapply SM0 with (lo := lo); rt_side idtac. }
  unfold ret_stF.
  after_call RT AF.
  lazymatch goal with |- cps _ (ASTA _ _ _ (eq (MS ?R ?FF ?pc ?fcx ?rv ?mm ?ro))) _ => change fcx with (frm_clear fc) end.
  lazymatch goal with AGx : agree_on (aclient _ _ _) ?ma ?mb |- _ =>
    obj_fwd_ag NOBJ AGx ltac:(fun b k a Hin Ha => right; right; left; exists b, k; split; [exact Hin| lia]) end.
  fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]).
  fframe_open RT AF PF (rt_live RT Σ) usp 0%nat 64 ltac:(fun Ha => exact (proj1 Ha)).
  lazymatch goal with H : rt_live RT ?S1 = rt_live RT Σ, F1 : rt_frames RT ?S1 = (fr, 0%nat) :: _ |- _ => rename H into LVX; rename S1 into Σx end.
  lazymatch goal with H : rt_sp0 RT Σx = rt_sp0 RT Σ |- _ => rename H into SPX end.
  fframe_chunk RT AF fr 0%nat 64 nas 32.
  fframe_chunk RT AF fr 0%nat 64 arr (4 * cap).
  (* [comment removed for export] *)
  lazymatch goal with A : ART RT Σx ?mm |- _ =>
    pose proof (proj2 (af_fshadow_apart RT AF Σx mm fr 0%nat A ltac:(rewrite FRS; left; reflexivity)) fr 0%nat ltac:(rewrite FRS; left; reflexivity)) as FSA;
    change (fs_size 0) with 64 in FSA; unfold shad, SHB in FSA end.
  refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
  (* [comment removed for export] *)
  walk_to AF MST [(usp + -208 + 56, usp + -208 + 64); (fr, fr + 24); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8)] [e_numaGetCount; 0xef498; 0xef468].
  cps_stop.
  art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
  lazymatch goal with AGFx : agree_on ?PFx _ ?mm, MUx : munch _ ?mm _ |- _ =>
    agf_munch AGFx MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
  lazymatch goal with MUx : munch _ ?ma ?mb, A : ART RT Σx ?ma |- _ =>
    obj_fwd NOBJ MUx ltac:(fun b k a Hin Ha =>
      pose proof (live_apart_seg RT AF Σx ma fr 0%nat b k a A ltac:(rewrite FRS; left; reflexivity) ltac:(rewrite LVX; exact Hin) Ha) as Hx;
      change (fs_size 0) with 64 in Hx; seg_side NAR ARR LOW LOR FRHI FR0 SP0W FRSEG FR64 FCD FCD0 FCD FCD0 FSA Hx) end.
  refresh RT AF. unfold shad, SHB in *.
  (* [comment removed for export] *)
  walk_to AF MST [(usp + -208 - 16, usp + -208)] [e_numaGetCount].
  eapply evt_cut.
  { lazymatch goal with |- evt _ _ (MS _ ?F0 _ ?fc0 None ?mm _) =>
      eapply (numaGetCount_evt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F0 fc0 mm (usp + -208) lo (rt_live RT Σ) nas cap arr vals) end.
    all: lazymatch goal with
         | |- numa_obj _ _ _ _ _ _ => exact NOBJ
         | |- acc _ _ _ _ => assumption
         | |- ro_cells _ _ _ _ => assumption
         | |- stk _ _ _ _ => assumption
         | |- mem_inv _ _ => assumption
         | |- _ => leaf_side NASH NAS FCD FCS FCD0 FCS0 FRSH FR64 LOR LOW SP0W SPB SP0Rb NAR ARR FRHI FR0 FRSEG
         end. }
  intros ms' PO. destruct PO as (a1q & a2q & mq & -> & MUl & WMl & MIl & STl).
  lazymatch type of MUl with munch _ ?ma ?mb =>
    lazymatch goal with A : ART RT ?S ma |- _ =>
      loop_art RT AF S mb lo MUl ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I]);
      loop_transport ma mb MUl ltac:(fun Hx => seg_side NAR ARR LOW LOR FRHI FR0 SP0W FRSEG FR64 FCD FCD0 FCD FCD0 FSA Hx);
      obj_fwd NOBJ MUl ltac:(fun b k a Hin Ha => pose proof (af_live_range RT AF Σ m b k ART0 Hin) as (_ & R & _); cbn [outside]; clear - R Ha LOW LOR;
                                unfold STACK_WIN, SEGTOP_A in *; repeat split; try exact I; lia) end end.
  fix_ret_pc.
  (* [comment removed for export] *)
  awalk [e_numaCreate].
  pose proof FR as FRrec. split_before FRrec (C8 s0) FRrec2. clear FRrec.
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); repeat split; try exact I; lia).
  pose proof NCR as NCR'. unfold numaCreate_cps in NCR'.
  eapply cps_seq.
  { eapply NCR' with (lo := lo) (n := 0) (ras := bv_unsigned ra :: ras); rt_side idtac.
    all: lazymatch goal with
         | |- s32 _ _ => split; [lia| reflexivity]
         | |- (_ <= _ <= _) => lia
         | |- uctx _ _ _ _ =>
             unfold uctx; rewrite ?unsigned_lit by ul;
             apply chain_ok_push with (fp1 := bv_unsigned s0);
             [ lia | clear - SPA; Z.div_mod_to_equations; lia | ul | exact (numaCreate_ra_range _ _ TR) | apply bv_unsigned_in_range
             | rewrite !Z_to_bv_bv_unsigned; lazymatch type of FRrec2 with rw_cells _ _ ?a _ => replace (usp + -16) with a by lia end; exact FRrec2
             | unfold usp; apply (chain_ok_keep ras m _ _ _ UC); eapply agree_sub; [exact AGF|]; cbv beta; intros zz Hzz; split; [left; ul| exact I] ]
         | |- numaCreate_trace_ok _ => exact TR
         | |- lenv _ _ _ _ _ _ => lenv_tac
         | |- lres _ _ _ _ _ => unfold numa_cap; cbn [Z.eqb]; change (mcost (4 * 50)) with 0; lres_tac9 LVP
         | |- ?g => idtac "LEFTOVER:" g
         end. }
  clear NCR' FRrec2.
  after_call RT AF.
  lazymatch goal with AGx : agree_on (fun a => aclient _ _ _ a /\ _) ?ma ?mb |- _ =>
    obj_fwd_ag NOBJ AGx ltac:(fun b k a Hin Ha => split; [right; right; left; exists b, k; split; [rewrite LVX; exact Hin| lia]| exact I]) end.
  fold_ag ltac:(fun Hx => pose proof (PFS _ Hx); destruct Hx as [Hx1 _]; split;
                [apply (aclient_mono _ _ usp _ _ _ _ Hx1); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]| exact I]).
  unfold numa_cap in *. cbn [Z.eqb] in *.
  lazymatch goal with H : rt_live RT ?S = numa_live ?p 50 ?q _ |- _ => rename H into LV2; rename S into Σ2; set (nad := p) in *; set (arrd := q) in * end.
  lazymatch goal with H : numa_obj _ _ nad 50 arrd [] |- _ => rename H into NOBJd end.
  rewrite LVX in LV2.
  lazymatch goal with H : rt_frames RT Σ2 = rt_frames RT Σx |- _ => rewrite FRS in H; rename H into FRS2 end.
  lazymatch goal with H : rt_sp0 RT Σ2 = rt_sp0 RT Σx |- _ => rewrite SPX in H; rename H into SP2 end.
  pose proof (numa_obj_facts _ _ _ _ _ _ NOBJd) as (_ & _ & ND0 & ND16 & AD0 & AD16 & INd & INad & NEd).
  chunk_facts RT AF GP nad 32. chunk_facts RT AF GP arrd 200.
  fframe_chunk RT AF fr 0%nat 64 nad 32. fframe_chunk RT AF fr 0%nat 64 arrd 200.
  (* [comment removed for export] *)
  split_at FRM 3%nat FRV. split_last_CB FRV [8%nat; 4%nat; 12%nat; 4%nat; 4%nat].
  split_at FRV 1%nat FRV1. clear FRV. split_at FRV1 1%nat FRV2. split_at FRV2 1%nat FRL. clear FRV2. split_at FRL 1%nat FRL2. clear FRL2.
  destruct (cb4_c4 _ _ _ FRV1) as (o1 & CSV). destruct (cb4_c4 _ _ _ FRL) as (o2 & CVL). clear FRV1 FRL.
  destruct (u32arr_nth vals 0 ltac:(lia)) as (w0 & Hw0).
  refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  local_acc FSH fr 4%nat 32 FR64 FR0 ACCSV. local_acc FSH fr 6%nat 48 FR64 FR0 ACCVL.
  (* [comment removed for export] *)
  walk_to AF MST [(usp + -208 - 16, usp + -208); (fr + 32, fr + 32 + 4)] [e_numaGetFValue].
  eapply evt_cut.
  { lazymatch goal with |- evt _ _ (MS _ ?F0 _ ?fc0 None ?mm _) =>
      eapply (numaGetFValue_evt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F0 fc0 mm (usp + -208) lo (rt_live RT Σ) nas cap arr vals 0 (fr + 32) w0 o1) end.
    all: lazymatch goal with
         | |- numa_obj _ _ _ _ _ _ => exact NOBJ
         | |- nth_error _ _ = _ => exact Hw0
         | |- acc _ _ _ _ => assumption
         | |- ro_cells _ _ _ _ => assumption
         | |- rw_cells _ _ _ _ => assumption
         | |- stk _ _ _ _ => assumption
         | |- mem_inv _ _ => assumption
         | |- _ => leaf_side NASH NAS FCD FCS FCD0 FCS0 FRSH FR64 LOR LOW SP0W SPB SP0Rb NAR ARR FRHI FR0 FRSEG
         end. }
  intros ms' PO. destruct PO as (b1 & b2 & b3 & b4 & b5 & b6 & b7 & F2 & mq2 & -> & MUl2 & WMl2 & MIl2 & STl2 & CSV2 & EF2).
  lazymatch type of MUl2 with munch _ ?ma ?mb =>
    lazymatch goal with A : ART RT ?S ma |- _ =>
      loop_art RT AF S mb lo MUl2 ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac| exact I]]);
      loop_transport ma mb MUl2 ltac:(fun Hx => seg_side NAR ARR LOW LOR FRHI FR0 SP0W FRSEG FR64 FCD FCD0 FCD1 FCD2 FSA Hx);
      obj_fwd NOBJ MUl2 ltac:(fun b k a Hin Ha =>
        pose proof (live_apart_seg RT AF Σ2 ma fr 0%nat b k a A ltac:(rewrite FRS2; left; reflexivity) ltac:(rewrite LV2; right; right; exact Hin) Ha) as Hx;
        change (fs_size 0) with 64 in Hx; seg_side NAR ARR LOW LOR FRHI FR0 SP0W FRSEG FR64 FCD FCD0 FCD1 FCD2 FSA Hx);
      obj_fwd NOBJd MUl2 ltac:(fun b k a Hin Ha =>
        pose proof (live_apart_seg RT AF Σ2 ma fr 0%nat b k a A ltac:(rewrite FRS2; left; reflexivity) Hin Ha) as Hx;
        change (fs_size 0) with 64 in Hx; seg_side NAR ARR LOW LOR FRHI FR0 SP0W FRSEG FR64 FCD FCD0 FCD1 FCD2 FSA Hx) end end.
  fix_ret_pc. subst F2.
  (* [comment removed for export] *)
  cps_stop.
  (* [comment removed for export] *)
  lazymatch type of FR with rw_cells _ ?mx ?A ?cs => let n := eval vm_compute in (Z.of_nat (cells_size cs)) in
    assert (FRW : wr_at asegs mx A n) by (exact (proj2 FR)) end.
  split_at FR 2%nat FRj. clear FR. split_at FRj 1%nat FRk. split_last_CB FRj [8%nat; 24%nat]. split_at FRj 1%nat FRn2. clear FRn2.
  destruct (cb8_c8 _ _ _ FRj) as (navw & NAVC). clear FRj. split_at FRk 2%nat FRsv. clear FRk.
  lazymatch goal with AGFx : agree_on ?PFx _ ?mm, MUx : munch _ ?mm _ |- _ =>
    agf_munch AGFx MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
  replace (mcost (4 * 50)) with 0 in * by reflexivity.
  eapply EXT_REST.
  all: lazymatch goal with
       | |- fdfs_only _ => exact FDO
       | |- mat_stable _ => exact MST
       | |- rt_live RT _ = _ => exact LV2
       | |- rt_frames RT _ = _ => exact FRS2
       | |- rt_sp0 RT _ = _ => exact SP2
       | |- ART _ _ _ => assumption
       | |- mem_inv _ _ => assumption
       | |- LIBH _ => assumption
       | |- io_ssp _ => assumption
       | |- stk _ _ _ _ => assumption
       | |- numa_obj _ _ _ _ _ [] => exact NOBJd
       | |- numa_obj _ _ _ _ _ _ => exact NOBJ
       | |- rw_cells _ _ (_ + 24) [C8 _] =>
           lazymatch type of NAVC with rw_cells _ _ ?b _ => lazymatch goal with |- rw_cells _ _ ?a _ => replace a with b by lia end end; exact NAVC
       | |- rw_cells _ _ _ _ => eassumption
       | |- wr_at _ _ _ _ => apply (wr_at_sub _ _ _ _ _ FRW); change (bv_unsigned sp) with usp; lia
       | |- agree_on _ _ _ => exact AGF
       | |- forall p n, In _ _ -> _ => exact LVP
       | |- _ => change (bv_unsigned sp) with usp; first [assumption | lia | clear - AL; Z.div_mod_to_equations; lia | unfold EXTREMA_COST, LSTK, RT_STACK in *; ul]
       end.
Qed.
End EXTPRE.
