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
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.B9 Require Import ImageA.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr FP.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.B9 Require Import Layout.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.B9 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit D_iface D_defs Lept_kit Lept_iface Lept_env LeptC_kit Lept_chain Lept_leaf Lept_objkit LeptL_kit Lept_fuzzkit Lept_gmax_defs Ed_fp Ed_iface Ed_fpkit Numa_kit Ed_numa_leaf Ed_ext_defs Ed_ext_kit Ed_ext_search Ed_ext_sweep.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section EXTMAIN.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis NAF : numaAddNumber_fast_cps RT.
Hypothesis NA : numaAddNumber_cps RT.

Lemma ext_rest_ok : ext_rest_stmt RT.
Proof using AF GP NAF NA.
  intros Σ Σ2 PMc m mm rae s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e fs0e fs1e fs2e gp s6x
         rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F1 fc1 sp usp0 lo fr nas cap arr nad arrd vals navw sv vl hd0 hd1 hd2
         FDO MST LV2 FRS2 SP2 CR2 ART2 MI LH SSP ST NOBJ NOBJd VLEN FRsv NAVC FRW FRM CSV CVL FSH AGF LOW LOR SPT SPA SPB USP0 USP0A FRB LVB CRB LVP.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned).
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  lazymatch type of AGF with agree_on ?P _ _ => set (PF := P) in * end.
  pose proof EGC_val as EGC. unfold EXTREMA_COST in CRB.
  destruct USP0 as [USPlo USPhi]. destruct VLEN as [VLa VLb].
  (* [comment removed for export] *)
  pose proof (af_frames_range RT AF Σ2 mm fr 0%nat ART2 ltac:(rewrite FRS2; left; reflexivity)) as (FR0 & FRHI & _ & _).
  pose proof (af_frames_align RT AF Σ2 mm fr 0%nat ART2 ltac:(rewrite FRS2; left; reflexivity)) as (FR64 & FRSEG).
  pose proof (af_frames_hi RT AF Σ2 mm fr 0%nat ART2 ltac:(rewrite FRS2; left; reflexivity)) as FRSH.
  change (fs_size 0) with 64 in FRHI, FRSH. rewrite SP2 in FRHI.
  pose proof (proj2 (af_fshadow_apart RT AF Σ2 mm fr 0%nat ART2 ltac:(rewrite FRS2; left; reflexivity)) fr 0%nat ltac:(rewrite FRS2; left; reflexivity)) as FSA.
  change (fs_size 0) with 64 in FSA. unfold shad, SHB in FSA.
  pose proof (af_sp0_range RT AF Σ2 mm ART2) as (SP0Ra & SP0Rb). pose proof (af_sp0_win RT AF Σ2 mm ART2) as SP0W. rewrite SP2 in SP0Ra, SP0Rb, SP0W.
  assert (NFA : forall a, PF a -> (a < fr \/ fr + 64 <= a) /\ (a < shad fr \/ shad (fr + 64) <= a)).
  { intros a [Ha _]. apply (new_frame_apart RT AF Σ2 mm fr 0%nat (rt_frames RT Σ) (rt_live RT Σ) usp a ART2 FRS2).
    - intros e He. rewrite LV2. right; right; exact He.
    - rewrite SP2. exact SPB.
    - rewrite SP2. unfold LSTK, RT_STACK in LOR. clear - LOW LOR. lia.
    - exact Ha. }
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a [Ha _]. destruct (aclient_split RT AF Σ2 mm usp a ART2) as [H|H].
    { rewrite LV2, FRS2. apply (aclient_mono _ _ usp _ _ _ _ Ha); [unfold numa_live; intros e He; right; right; exact He| intros e He; right; exact He| clear; lia]. }
    { left; exact H. }
    { right. rewrite SP2 in H. clear - H LOW. lia. } }
  unfold LSTK, STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  (* [comment removed for export] *)
  assert (EPI : forall (Σ' : rts RT) (m' : mem) (ra' t0' t1' t2' s1' a0' a1' a2' a3' a4' a5' a6' a7' s3' s5' s6' s7' s8' s9' t3' t4' t5' t6' : word)
                       (F' : bvmap 5 word) (fc' : bv 32) (capd' arrd' : Z) (vd' : list word) (h0 h1 h2 : word),
    rt_live RT Σ' = numa_live nad capd' arrd' (rt_live RT Σ) -> rt_frames RT Σ' = (fr, 0%nat) :: rt_frames RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ ->
    rt_credit RT Σ - 1 - EXTREMA_GROWTH_COST <= rt_credit RT Σ' ->
    Z.of_nat (length vd') + 1 <= Z.max 1 (Z.of_nat (length vals)) ->
    numa_obj (rt_live RT Σ') m' nad capd' arrd' vd' ->
    ART RT Σ' m' -> mem_inv asegs m' -> LIBH m' -> io_ssp m' -> stk asegs m' lo usp0 ->
    rw_cells asegs m' (usp + -128) [C8 fs2e; C8 fs1e; C8 fs0e; C8 s11e; C8 s10e; C8 s9e; C8 s8e; C8 s7e; C8 s6e; C8 s5e; C8 s4e; C8 s3e; C8 s2e; C8 s1e; C8 s0e; C8 rae] ->
    wr_at asegs m' usp0 (usp - usp0) ->
    rw_cells asegs m' fr [C8 h0; C8 h1; C8 h2] -> rw_cells asegs m' (fr / 8 + 2147450880) ext_shadow ->
    agree_on PF m m' ->
    cps asegs (ASTA RT Σ' PMc (eq (MS (mkR ra' (Z_to_bv 64 usp0) gp (Z_to_bv 64 TP_A) t0' t1' t2' (Z_to_bv 64 usp) s1' a0' a1' a2' a3' a4' a5' a6' a7'
                                          (Z_to_bv 64 fr) s3' (Z_to_bv 64 nad) s5' s6' s7' s8' s9' (Z_to_bv 64 fr) (Z_to_bv 64 (fr / 8 + 2147450880)) t3' t4' t5' t6')
                                     F' (Z_to_bv 64 0xef680) (frm_clear fc') None m' (seg_rom asegs)))) QF).
  { clear ART2 MI LH SSP ST NOBJ NOBJd FRsv NAVC FRW FRM CSV CVL FSH AGF LV2 FRS2 SP2 CR2.
    intros Σ' m' ra' t0' t1' t2' s1' a0' a1' a2' a3' a4' a5' a6' a7' s3' s5' s6' s7' s8' s9' t3' t4' t5' t6' F' fc' capd' arrd' vd' h0 h1 h2
      LV' FRS SP' CR' LVD' NOBJd' ART' MI' LH' SSP' ST' FRsv' FRW' FRM' FSH' AGF.
    pose proof (numa_obj_facts _ _ _ _ _ _ NOBJd') as (_ & CAPd & ND0 & ND16 & AD0 & AD16 & INd & INad & NEd).
    unfold ext_shadow in FSH'.
    pose proof ST' as (STa & STb & _).
    refresh RT AF. unfold shad, SHB in *. park_disj.
    walk_to AF MST [(fr, fr + 8); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8)] [0xef6cc; 0xef6ec].
    obj_fwd NOBJd' MU ltac:(fun b k a Hin Ha =>
      pose proof (live_apart_seg RT AF Σ' m' fr 0%nat b k a ART' ltac:(rewrite FRS; left; reflexivity) Hin Ha) as Hx;
      change (fs_size 0) with 64 in Hx; unfold shad, SHB in Hx; cbn [outside]; clear - Hx FR64; repeat split; try exact I; Z.div_mod_to_equations; lia).
    frame_release_w RT AF GP MST Σ fr 0%nat 64 PF AGF PFS usp lo 0xef6ec
        ltac:(cbn [ivls_client]; split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]])
        ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2];
                        unfold shad, SHB in *; repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia])
        ltac:(fun Hx => exact (proj1 Hx))
        ltac:(fun fl FLN =>
                assert (FLL : forall b k a, In (b, k) (rt_live RT Σ') -> b <= a < b + k -> outside [(fl, fl + 1)] a)
                  by (intros b k a Hin Ha; cbn [outside]; split; [| exact I]; intros Hfl; apply FLN; replace fl with a by lia;
                      right; right; left; exists b, k; split; assumption)).
    lazymatch goal with MUx : munch [(_, _ + 1)] _ _ |- _ => obj_fwd NOBJd' MUx ltac:(fun b k a Hin Ha => exact (FLL b k a Hin Ha)) end.
    walk_to AF MST (@nil (Z * Z)) (@nil Z).
    cps_stop.
    lazymatch goal with |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mf _))) _ =>
      assert (STF : stk asegs mf lo usp)
        by (lazymatch goal with W : wr_at asegs mf usp0 _, S : stk asegs mf lo usp0 |- _ =>
              let S1 := fresh "S1" in pose proof (wr_at_stk _ _ _ W) as S1; replace (usp0 + (usp - usp0)) with usp in S1 by (clear; lia);
              exact (stk_merge asegs _ lo usp0 usp S S1 ltac:(clear - USPlo USPhi LOR; lia)) end) end.
    apply cps_finish. intros c Hc. subst QF. unfold ext_post.
    exists S2, nad, capd', arrd', vd'.
    split; [| split; [exact LVD'| split; [rewrite LV2; exact LV'| split; [exact FRS2| split; [rewrite SP2; exact SP'| rewrite CR2; unfold EXTREMA_COST; clear - CR' EGC; lia]]]]].
    eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-. eexists.
    split; [unfold ret_st; rewrite ?ESP; do 16 eexists; reflexivity|].
    split.
    { unfold lpost_f, rt_after_f. fold usp. split; [split; [assumption| split; [assumption| exact STF]]| split; assumption]. }
    split.
    { unfold keepsL, rt_pres_fp. fold usp. intros a Ha Ho. exact (AGF a (conj Ha Ho)). }
    rewrite LV2. exact NOBJd'. }
  (* [comment removed for export] *)
  pose proof (numa_obj_facts _ _ _ _ _ _ NOBJ) as (LEN & CAP & NA0 & NA16 & AR0 & AR16 & INn & INa & NE).
  pose proof (numa_obj_facts _ _ _ _ _ _ NOBJd) as (_ & _ & ND0 & ND16 & AD0 & AD16 & INd & INad & NEd).
  assert (INnS : In (nas, 32) (rt_live RT Σ2)) by (rewrite LV2; right; right; exact INn).
  assert (INaS : In (arr, 4 * cap) (rt_live RT Σ2)) by (rewrite LV2; right; right; exact INa).
  chunk_named RT AF GP nas 32 NAR NASEG NASH. chunk_named RT AF GP arr (4 * cap) ARR ARSEG ARSH.
  chunk_named RT AF GP nad 32 NDR NDSEG NDSH. chunk_named RT AF GP arrd (4 * 50) ADR ADSEG ADSH.
  fframe_named RT AF fr 0%nat 64 nas 32 FCn FSn. fframe_named RT AF fr 0%nat 64 arr (4 * cap) FCa FSa.
  fframe_named RT AF fr 0%nat 64 nad 32 FCd FSd. fframe_named RT AF fr 0%nat 64 arrd (4 * 50) FCad FSad.
  pose proof ST as (STa & STb & _).
  refresh RT AF. unfold shad, SHB in *. park_disj.
  unfold ext_shadow in FSH.
  local_acc FSH fr 6%nat 48 FR64 FR0 ACCv.
  walk_to AF MST [(usp0 + 24, usp0 + 24 + 8)] [0xef680; 0xef558].
  destruct (Z_lt_ge_dec (Z.of_nat (length vals)) 2) as [N1|N2].
  { (* [comment removed for export] *)
    brT. cps_stop.
    lazymatch goal with |- cps _ (ASTA _ _ _ (eq (MS _ ?FF _ (frm_clear ?fcx) _ ?mx _))) _ =>
      eapply (EPI Σ2 mx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FF fcx 50 arrd [] hd0 hd1 hd2) end.
    all: first [assumption | cbn [length]; lia]. }
  brF.
  awalk [0xef680; 0xef558].
  (* [comment removed for export] *)
  assert (LOR0 : lo + (65536 + 1024 * 5) + 16 <= usp0) by (clear - LOR USPlo; lia).
  cps_stop.
  art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I]).
  lazymatch goal with MUx : munch [(_ + 24, _)] ?ma ?mb |- _ =>
    obj_fwd NOBJ MUx ltac:(fun b k a Hin Ha =>
      pose proof (live_apart_seg RT AF Σ2 ma fr 0%nat b k a ART2 ltac:(rewrite FRS2; left; reflexivity) ltac:(rewrite LV2; right; right; exact Hin) Ha) as (L1 & _);
      rewrite SP2 in L1; unfold STACK_WIN in L1; cbn [outside]; clear - L1 LOW LOR0; repeat split; try exact I; lia);
    obj_fwd NOBJd MUx ltac:(fun b k a Hin Ha =>
      pose proof (live_apart_seg RT AF Σ2 ma fr 0%nat b k a ART2 ltac:(rewrite FRS2; left; reflexivity) Hin Ha) as (L1 & _);
      rewrite SP2 in L1; unfold STACK_WIN in L1; cbn [outside]; clear - L1 LOW LOR0; repeat split; try exact I; lia);
    agf_munch AGF MUx ltac:(fun Hx => pose proof (PFS _ Hx) as HxS; revert HxS; clear - LOR USPlo USPhi; cbn [outside]; intros HxS; repeat split; try exact I; lia) end.
  cps_walk AF MST.
  (* [comment removed for export] *)
  cps_stop.
  walk_to AF MST [(usp0 - 16, usp0); (fr + 48, fr + 48 + 4)] [0xef558].
  assert (LAP : forall b kk a, In (b, kk) (rt_live RT Σ) -> b <= a < b + kk -> a < lo /\ (a < fr \/ fr + 64 <= a)).
  { intros b kk a Hin Ha.
    pose proof (live_apart_seg RT AF Σ2 mm fr 0%nat b kk a ART2 ltac:(rewrite FRS2; left; reflexivity) ltac:(rewrite LV2; right; right; exact Hin) Ha) as (X1 & X2 & _).
    change (fs_size 0) with 64 in X2. rewrite SP2 in X1. unfold STACK_WIN in X1. clear - X1 X2 LOW. split; [lia| exact X2]. }
  eapply evt_cut.
  { lazymatch goal with |- evt _ _ (MS _ ?F0 _ (frm_clear ?fc0) None ?mx _) =>
      eapply (ext_search (Z.to_nat (Z.of_nat (length vals) - 1)) 1 _ gp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F0 fc0 mx usp usp0 fr lo nas cap arr nad vals (rt_live RT Σ) sv vl) end.
    all: lazymatch goal with
         | |- numa_obj _ _ _ _ _ _ => exact NOBJ
         | |- acc _ _ _ _ => assumption
         | |- ro_cells _ _ _ _ => assumption
         | |- rw_cells _ _ _ _ => assumption
         | |- stk _ _ _ _ => assumption
         | |- mem_inv _ _ => assumption
         | |- forall _ _ _, _ => exact LAP
         | |- _ mod _ = 0 => exact FR64
         | |- _ => unfold parked, SEGTOP_A in *; clear - N2 VLa VLb FR0 FR64 LOR USPlo USPhi SPT LOW SP0W NAR ARR FRHI FRSEG NASEG NASH ARSEG ARSH FRSH FCn FCa; lia
         end. }
  intros ms' PO.
  destruct PO as (found & i' & c1 & c2 & c3 & c4 & c5 & c6 & c7 & c8 & c9 & c10 & c11 & c12 & c13 & c14 & c15 & c16 & F' & fc' & m1 & vl' & -> & HI' & MUl & WMl & MIl & STl & CVL1).
  lazymatch type of MUl with munch _ ?ma ?mb =>
    lazymatch goal with A : ART RT ?S ma |- _ =>
      loop_art RT AF S mb lo MUl ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac| exact I]]);
      loop_transport ma mb MUl ltac:(fun Hx => seg_side NAR ARR LOW LOR0 FRHI FR0 SP0W FRSEG FR64 FCn FCa USPhi FCad FSA Hx);
      obj_fwd NOBJ MUl ltac:(fun b k a Hin Ha =>
        pose proof (live_apart_seg RT AF S ma fr 0%nat b k a A ltac:(rewrite FRS2; left; reflexivity) ltac:(rewrite LV2; right; right; exact Hin) Ha) as Hx;
        change (fs_size 0) with 64 in Hx; rewrite SP2 in Hx; seg_side NAR ARR LOW LOR0 FRHI FR0 SP0W FRSEG FR64 FCn FCa USPhi FCad FSA Hx);
      obj_fwd NOBJd MUl ltac:(fun b k a Hin Ha =>
        pose proof (live_apart_seg RT AF S ma fr 0%nat b k a A ltac:(rewrite FRS2; left; reflexivity) Hin Ha) as Hx;
        change (fs_size 0) with 64 in Hx; rewrite SP2 in Hx; seg_side NAR ARR LOW LOR0 FRHI FR0 SP0W FRSEG FR64 FCn FCa USPhi FCad FSA Hx) end end.
  agf_munch AGF MU ltac:(fun Hx => pose proof (PFS _ Hx) as HxS; destruct (NFA _ Hx) as [N1 _]; revert HxS N1; clear - LOR USPlo USPhi; cbn [outside]; intros HxS N1; repeat split; try exact I; lia).
  destruct found.
  2: { (* [comment removed for export] *)
    cbv iota. subst i'. cps_stop.
    lazymatch goal with |- cps _ (ASTA _ _ _ (eq (MS _ ?FF _ (frm_clear ?fcx) _ ?mx _))) _ =>
      eapply (EPI Σ2 mx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FF fcx 50 arrd [] hd0 hd1 hd2) end.
    all: first [assumption | cbn [length]; lia]. }
  cbv iota. destruct HI' as [HIa HIb].
  awalk [0xef680; 0xef5c0; 0xef59c].
  rewrite ?swrap32_small by (clear - HIa HIb VLb; lia).
  destruct (Z_lt_ge_dec (i' + 1) (Z.of_nat (length vals))) as [NX|NX].
  2: { (* [comment removed for export] *)
    brT. cps_stop.
    lazymatch goal with |- cps _ (ASTA _ _ _ (eq (MS _ ?FF _ (frm_clear ?fcx) _ ?mx _))) _ =>
      eapply (EPI Σ2 mx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FF fcx 50 arrd [] hd0 hd1 hd2) end.
    all: first [assumption | cbn [length]; lia]. }
  brF.
  (* [comment removed for export] *)
  cps_stop.
  walk_to AF MST [(usp0 + 24, usp0 + 24 + 8)] [0xef59c].
  step.
  lazymatch goal with |- evt _ _ (MS _ ?FF _ _ _ _ _) => remember FF as F2 eqn:EF2; clear EF2 end.
  fbr.
  all: awalk [0xef5c0].
  all: lazymatch goal with |- context [Z_to_bv 64 (Z.lor ?a ?b)] => let v := eval vm_compute in (Z.lor a b) in change (Z.lor a b) with v end.
  all: try replace (Z_to_bv 64 18446744073709551615) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity).
  all: cps_stop.
  all: art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I]).
  all: lazymatch goal with MUx : munch [(_ + 24, _)] ?ma ?mb |- _ =>
         obj_fwd NOBJ MUx ltac:(fun b k a Hin Ha => destruct (LAP b k a Hin Ha) as [L1 _]; cbn [outside]; clear - L1 LOR0; repeat split; try exact I; lia);
         obj_fwd NOBJd MUx ltac:(fun b k a Hin Ha =>
           pose proof (live_apart_seg RT AF Σ2 ma fr 0%nat b k a ARTl ltac:(rewrite FRS2; left; reflexivity) Hin Ha) as (L1 & _);
           rewrite SP2 in L1; unfold STACK_WIN in L1; cbn [outside]; clear - L1 LOW LOR0; repeat split; try exact I; lia);
         agf_munch AGF MUx ltac:(fun Hx => pose proof (PFS _ Hx) as HxS; revert HxS; clear - LOR USPlo USPhi; cbn [outside]; intros HxS; repeat split; try exact I; lia) end.
  (* [comment removed for export] *)
  { eapply cps_seq.
    { lazymatch goal with |- cps _ (ASTA _ _ _ (eq (MS _ ?FF _ (frm_clear ?fcx) _ ?mx _))) _ =>
        eapply (ext_sweep RT AF GP NAF NA (Z.to_nat (Z.of_nat (length vals) - (i' + 1))) (i' + 1) Σ2 PMc mx _ gp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FF fcx
                  usp usp0 fr lo nas cap arr nad 50 arrd i' _ (rt_sp0 RT Σ) (rt_credit RT Σ2) vals [] (rt_live RT Σ) (rt_frames RT Σ) vl') end.
      all: lazymatch goal with
           | |- fdfs_only _ => exact FDO
           | |- mat_stable _ => exact MST
           | |- rt_live _ _ = _ => exact LV2
           | |- rt_frames _ _ = _ => exact FRS2
           | |- rt_sp0 _ _ = _ => exact SP2
           | |- In _ CAPS => left; reflexivity
           | |- _ \/ _ => first [left; reflexivity | right; reflexivity | unfold parked in *; assumption]
           | |- numa_obj _ _ _ _ _ [] => exact NOBJd
           | |- numa_obj _ _ _ _ _ _ => exact NOBJ
           | |- rw_cells _ _ _ _ => first [assumption | unfold ext_shadow; assumption]
           | |- LIBH _ => assumption
           | |- io_ssp _ => assumption
           | |- ART _ _ _ => assumption
           | |- mem_inv _ _ => assumption
           | |- stk _ _ _ _ => assumption
           | |- forall _ _, _ => exact LVP
           | |- _ mod 64 = 0 => exact FR64
           | |- _ mod 16 = 0 => clear - USP0A; Z.div_mod_to_equations; lia
           | |- _ => first [assumption | change (ext_spent 50) with 0; cbv delta [LSTK RT_STACK STACK_WIN USTACK_TOP SEGTOP_A]; cbv beta; cbn [length];
                            clear - NX HIa HIb VLb CR2 CRB EGC LOR USPlo USPhi SPT SPB LOW FR0 FRHI FRSEG FRB LVB; lia]
           end. }
    after_call RT AF.
    fold_ag ltac:(fun Hx => destruct (NFA _ Hx) as [N1 _]; destruct Hx as [Hx _]; split;
                  [apply (aclient_mono _ _ usp _ _ _ _ Hx); [intros e He; exact He| intros e He; right; exact He| clear - USPhi; lia]
                  | revert N1; clear; cbn [outside]; intros N1; repeat split; try exact I; lia]).
    lazymatch goal with H : rt_live RT ?S = numa_live nad ?c ?a _, NO : numa_obj (rt_live RT ?S) ?mx nad ?c ?a ?v |- cps _ (ASTA RT ?S _ (eq (MS _ ?FF _ (frm_clear ?fcx) _ ?mx _))) _ =>
      eapply (EPI S mx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FF fcx c a v hd0 hd1 hd2) end.
    all: first [assumption | idtac].
    all: lazymatch goal with
         | |- _ <= rt_credit _ _ => lazymatch goal with C : rt_credit _ _ - EXTREMA_GROWTH_COST <= rt_credit _ _ |- _ => clear - C CR2; lia end
         | |- _ <= Z.max _ _ => lazymatch goal with C : Z.of_nat (length _) <= Z.of_nat (length _) - 2 |- _ => clear - C; lia end
         end. }
  { eapply cps_seq.
    { lazymatch goal with |- cps _ (ASTA _ _ _ (eq (MS _ ?FF _ (frm_clear ?fcx) _ ?mx _))) _ =>
        eapply (ext_sweep RT AF GP NAF NA (Z.to_nat (Z.of_nat (length vals) - (i' + 1))) (i' + 1) Σ2 PMc mx _ gp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FF fcx
                  usp usp0 fr lo nas cap arr nad 50 arrd i' _ (rt_sp0 RT Σ) (rt_credit RT Σ2) vals [] (rt_live RT Σ) (rt_frames RT Σ) vl') end.
      all: lazymatch goal with
           | |- fdfs_only _ => exact FDO
           | |- mat_stable _ => exact MST
           | |- rt_live _ _ = _ => exact LV2
           | |- rt_frames _ _ = _ => exact FRS2
           | |- rt_sp0 _ _ = _ => exact SP2
           | |- In _ CAPS => left; reflexivity
           | |- _ \/ _ => first [left; reflexivity | right; reflexivity | unfold parked in *; assumption]
           | |- numa_obj _ _ _ _ _ [] => exact NOBJd
           | |- numa_obj _ _ _ _ _ _ => exact NOBJ
           | |- rw_cells _ _ _ _ => first [assumption | unfold ext_shadow; assumption]
           | |- LIBH _ => assumption
           | |- io_ssp _ => assumption
           | |- ART _ _ _ => assumption
           | |- mem_inv _ _ => assumption
           | |- stk _ _ _ _ => assumption
           | |- forall _ _, _ => exact LVP
           | |- _ mod 64 = 0 => exact FR64
           | |- _ mod 16 = 0 => clear - USP0A; Z.div_mod_to_equations; lia
           | |- _ => first [assumption | change (ext_spent 50) with 0; cbv delta [LSTK RT_STACK STACK_WIN USTACK_TOP SEGTOP_A]; cbv beta; cbn [length];
                            clear - NX HIa HIb VLb CR2 CRB EGC LOR USPlo USPhi SPT SPB LOW FR0 FRHI FRSEG FRB LVB; lia]
           end. }
    after_call RT AF.
    fold_ag ltac:(fun Hx => destruct (NFA _ Hx) as [N1 _]; destruct Hx as [Hx _]; split;
                  [apply (aclient_mono _ _ usp _ _ _ _ Hx); [intros e He; exact He| intros e He; right; exact He| clear - USPhi; lia]
                  | revert N1; clear; cbn [outside]; intros N1; repeat split; try exact I; lia]).
    lazymatch goal with H : rt_live RT ?S = numa_live nad ?c ?a _, NO : numa_obj (rt_live RT ?S) ?mx nad ?c ?a ?v |- cps _ (ASTA RT ?S _ (eq (MS _ ?FF _ (frm_clear ?fcx) _ ?mx _))) _ =>
      eapply (EPI S mx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FF fcx c a v hd0 hd1 hd2) end.
    all: first [assumption | idtac].
    all: lazymatch goal with
         | |- _ <= rt_credit _ _ => lazymatch goal with C : rt_credit _ _ - EXTREMA_GROWTH_COST <= rt_credit _ _ |- _ => clear - C CR2; lia end
         | |- _ <= Z.max _ _ => lazymatch goal with C : Z.of_nat (length _) <= Z.of_nat (length _) - 2 |- _ => clear - C; lia end
         end. }
Qed.
End EXTMAIN.
