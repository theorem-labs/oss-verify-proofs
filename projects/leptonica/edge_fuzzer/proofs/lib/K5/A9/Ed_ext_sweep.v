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
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr FP.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.A9 Require Import Layout.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.A9 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit D_iface D_defs Lept_kit Lept_iface Lept_env LeptC_kit Lept_chain Lept_leaf Lept_objkit LeptL_kit Lept_fuzzkit Lept_gmax_defs Ed_fp Ed_iface Ed_fpkit Numa_kit Ed_numa_leaf Ed_ext_defs Ed_ext_kit.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section SWEEP.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis NAF : numaAddNumber_fast_cps RT.
Hypothesis NA : numaAddNumber_cps RT.

(* [comment removed for export] *)
Definition sweep_kept (L : list (Z * Z)) (frames : list (Z * nat)) (usp0 fr : Z) (a : Z) : Prop :=
  aclient L ((fr, 0%nat) :: frames) usp0 a /\ outside [(fr + 48, fr + 48 + 4)] a.

Definition sweep_post PMc (gp : word) (usp usp0 fr nas nad n lo sp0 cr0 : Z) (L : list (Z * Z)) (frames : list (Z * nat)) (cap arr : Z) (vals : list word)
    (mc : mem) : config -> Prop :=
  fun c => exists (Σ' : rts RT) (capd' arrd' loc' dir' : Z) (vd' : list word) (vl' : word),
    ASTA RT Σ' PMc (fun ms => exists (m' : mem) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32),
        ms = MS (mkR ra' (Z_to_bv 64 usp0) gp (Z_to_bv 64 TP_A) t0' t1' t2' (Z_to_bv 64 usp) (Z_to_bv 64 usp0) a0' a1' a2' a3' a4' a5' a6' a7'
                     (Z_to_bv 64 fr) (Z_to_bv 64 nas) (Z_to_bv 64 nad) (Z_to_bv 64 n) (Z_to_bv 64 dir') (Z_to_bv 64 (fr + 48)) (Z_to_bv 64 n)
                     (Z_to_bv 64 loc') (Z_to_bv 64 fr) (Z_to_bv 64 (fr / 8 + SHB)) t3' t4' t5' t6')
                F' (Z_to_bv 64 0xeea98) (frm_clear fc') None m' (seg_rom asegs)
        /\ rt_after_f RT Σ' usp0 lo mc m'
        /\ rt_pres_fp L ((fr, 0%nat) :: frames) usp0 [(fr + 48, fr + 48 + 4)] mc m'
        /\ LIBH m' /\ io_ssp m'
        /\ numa_obj (rt_live RT Σ') m' nad capd' arrd' vd' /\ numa_obj L m' nas cap arr vals
        /\ rw_cells asegs m' (fr + 48) [C4 vl']) c
    /\ rt_live RT Σ' = numa_live nad capd' arrd' L /\ rt_frames RT Σ' = (fr, 0%nat) :: frames /\ rt_sp0 RT Σ' = sp0
    /\ cr0 - EXTREMA_GROWTH_COST <= rt_credit RT Σ'
    /\ Z.of_nat (length vd') <= n - 2.

Lemma ext_sweep : forall (k : nat) (i : Z) (Σi : rts RT) PMc (mc : mem)
    (ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (usp usp0 fr lo nas cap arr nad capd arrd loc dir sp0 cr0 : Z) (vals vd : list word) (L : list (Z * Z)) (frames : list (Z * nat)) (vl : word),
  Z.of_nat k = Z.of_nat (length vals) - i -> 2 <= i < Z.of_nat (length vals) -> Z.of_nat (length vals) <= 20000 ->
  fdfs_only PMc -> mat_stable PMc ->
  rt_live RT Σi = numa_live nad capd arrd L -> rt_frames RT Σi = (fr, 0%nat) :: frames -> rt_sp0 RT Σi = sp0 ->
  In capd CAPS -> Z.of_nat (length vd) <= i - 2 -> cr0 - ext_spent capd <= rt_credit RT Σi -> EXTREMA_GROWTH_COST + 3 <= cr0 ->
  (dir = 1 \/ dir = -1) ->
  numa_obj L mc nas cap arr vals -> numa_obj (rt_live RT Σi) mc nad capd arrd vd ->
  rw_cells asegs mc (fr + 48) [C4 vl] -> rw_cells asegs mc (usp0 + 24) [C8 (Z_to_bv 64 0)] -> rw_cells asegs mc (fr / 8 + SHB) ext_shadow ->
  LIBH mc -> io_ssp mc -> ART RT Σi mc -> mem_inv asegs mc -> stk asegs mc lo usp0 ->
  sp0 - STACK_WIN <= lo -> lo + LSTK 5 + 16 <= usp0 -> usp0 + 16 <= USTACK_TOP -> usp0 mod 16 = 0 -> usp0 + 192 <= sp0 -> usp0 + 192 <= usp ->
  0 < fr -> fr mod 64 = 0 -> fr + 64 <= sp0 - STACK_WIN -> SEGTOP_A <= fr -> (fr + 64 <= 0x7fff7000 \/ 0x10007fff8000 <= fr) ->
  Z.of_nat (length frames) + 1 <= Z.of_nat FRAMES_MAX -> Z.of_nat (length L) + 3 <= LIVE_MAX -> (forall p n, In (p, n) L -> 0 < n) ->
  cps asegs (ASTA RT Σi PMc (eq (MS (mkR ra (Z_to_bv 64 usp0) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 usp0) a0 a1 a2 a3 a4 a5 a6 a7
                                        (Z_to_bv 64 fr) (Z_to_bv 64 nas) (Z_to_bv 64 nad) (Z_to_bv 64 (Z.of_nat (length vals))) (Z_to_bv 64 dir)
                                        (Z_to_bv 64 (fr + 48)) (Z_to_bv 64 i) (Z_to_bv 64 loc) (Z_to_bv 64 fr) (Z_to_bv 64 (fr / 8 + SHB)) t3 t4 t5 t6)
                                   F (Z_to_bv 64 0xee9d8) (frm_clear fc) None mc (seg_rom asegs))))
    (sweep_post PMc gp usp usp0 fr nas nad (Z.of_nat (length vals)) lo sp0 cr0 L frames cap arr vals mc).
Proof using AF GP NAF NA.
  induction k as [|k IH]; intros i Σi PMc mc ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc usp usp0 fr lo nas cap arr nad capd arrd loc dir sp0 cr0 vals vd L frames vl
    HK HI VLEN FDO MST LVi FRSi SPi HCAP LVD CRi CR0 DIR NOBJ NOBJd CVL NAVC FSH LH SSP ART0 MI ST LOW LOR SPT SPA SPB SPU FR0 FR64 FRHI FRSEG FRSH FRB LVB LVP.
  { exfalso. lia. }
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  set (PF := sweep_kept L frames usp0 fr).
  pose proof EGC_val as EGC.
  (* [comment removed for export] *)
  assert (TAIL : forall (Σ' : rts RT) (m' : mem) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32)
                        (capd' arrd' loc' dir' : Z) (vd' : list word) (vl' : word),
    rt_live RT Σ' = numa_live nad capd' arrd' L -> rt_frames RT Σ' = (fr, 0%nat) :: frames -> rt_sp0 RT Σ' = sp0 ->
    In capd' CAPS -> Z.of_nat (length vd') <= i - 1 -> cr0 - ext_spent capd' <= rt_credit RT Σ' -> (dir' = 1 \/ dir' = -1) ->
    numa_obj L m' nas cap arr vals -> numa_obj (rt_live RT Σ') m' nad capd' arrd' vd' ->
    rw_cells asegs m' (fr + 48) [C4 vl'] -> rw_cells asegs m' (usp0 + 24) [C8 (Z_to_bv 64 0)] -> rw_cells asegs m' (fr / 8 + SHB) ext_shadow ->
    LIBH m' -> io_ssp m' -> ART RT Σ' m' -> mem_inv asegs m' -> stk asegs m' lo usp0 ->
    agree_on PF mc m' ->
    cps asegs (ASTA RT Σ' PMc (eq (MS (mkR ra' (Z_to_bv 64 usp0) gp (Z_to_bv 64 TP_A) t0' t1' t2' (Z_to_bv 64 usp) (Z_to_bv 64 usp0) a0' a1' a2' a3' a4' a5' a6' a7'
                                          (Z_to_bv 64 fr) (Z_to_bv 64 nas) (Z_to_bv 64 nad) (Z_to_bv 64 (Z.of_nat (length vals))) (Z_to_bv 64 dir')
                                          (Z_to_bv 64 (fr + 48)) (Z_to_bv 64 i) (Z_to_bv 64 loc') (Z_to_bv 64 fr) (Z_to_bv 64 (fr / 8 + SHB)) t3' t4' t5' t6')
                                     F' (Z_to_bv 64 0xee9d0) (frm_clear fc') None m' (seg_rom asegs)))) QF).
  { intros Σ' m' ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' capd' arrd' loc' dir' vd' vl'
      LV' FRS' SP' HCAP' LVD' CR' DIR' NOBJ' NOBJd' CVL' NAVC' FSH' LH' SSP' ART' MI' ST' AGF'.
    cps_walk AF MST.
    step. step. rewrite (unsigned_lit i) by lia. rewrite swrap32_small by lia.
    destruct (Z.eq_dec (i + 1) (Z.of_nat (length vals))) as [EQ|NEQ].
    - (* [comment removed for export] *)
      rewrite <- EQ. brT. rewrite EQ.
      cps_stop. apply cps_finish. intros c Hc. subst QF. unfold sweep_post.
      exists Σ', capd', arrd', loc', dir', vd', vl'.
      split; [| split; [exact LV'| split; [exact FRS'| split; [exact SP'| split; [pose proof (ext_spent_le capd'); lia| lia]]]]].
      eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-.
      exists m', ra', t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', F', fc'.
      split; [reflexivity|].
      split; [exact (conj ART' (conj MI' ST'))|].
      split; [intros a Ha Ho; exact (AGF' a (conj Ha Ho))|].
      split; [exact LH'|]. split; [exact SSP'|]. split; [exact NOBJd'|]. split; [exact NOBJ'| exact CVL'].
    - (* [comment removed for export] *)
      brF.
      cps_stop.
      eapply cps_conseq; [ | intros c Hc; exact Hc | ].
      + eapply (IH (i + 1) Σ' PMc m' ra' gp t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' usp usp0 fr lo nas cap arr nad capd' arrd' loc' dir' sp0 cr0
                   vals vd' L frames vl'); first [assumption | lia].
      + intros c (Σ2 & capd2 & arrd2 & loc2 & dir2 & vd2 & vl2 & HA & L2 & F2 & S2 & C2 & N2). subst QF. unfold sweep_post.
        exists Σ2, capd2, arrd2, loc2, dir2, vd2, vl2.
        split; [| split; [exact L2| split; [exact F2| split; [exact S2| split; [exact C2| exact N2]]]]].
        eapply (ASTA_conseq RT); [exact HA|]. cbv beta.
        intros ms (m2 & ra2 & t02 & t12 & t22 & a02 & a12 & a22 & a32 & a42 & a52 & a62 & a72 & t32 & t42 & t52 & t62 & Fx & fcx & E & RA & P & R).
        exists m2, ra2, t02, t12, t22, a02, a12, a22, a32, a42, a52, a62, a72, t32, t42, t52, t62, Fx, fcx.
        split; [exact E|]. split; [exact RA|].
        split; [intros a Ha Ho; rewrite (P a Ha Ho); exact (AGF' a (conj Ha Ho))| exact R]. }
  pose proof (caps_facts capd HCAP) as (CAPB & CAP2 & CAPC).
  pose proof (numa_obj_facts _ _ _ _ _ _ NOBJ) as (LEN & CAP & NA0 & NA16 & AR0 & AR16 & INn & INa & NE).
  pose proof (numa_obj_facts _ _ _ _ _ _ NOBJd) as (LEND & _ & ND0 & ND16 & AD0 & AD16 & INd & INad & NEd).
  assert (INnS : In (nas, 32) (rt_live RT Σi)) by (rewrite LVi; right; right; exact INn).
  assert (INaS : In (arr, 4 * cap) (rt_live RT Σi)) by (rewrite LVi; right; right; exact INa).
  destruct (af_client_consts RT AF Σi mc ART0) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF Σi mc ART0) as (SP0Ra & SP0Rb). pose proof (af_sp0_win RT AF Σi mc ART0) as SP0W. rewrite SPi in *.
  chunk_named RT AF GP nas 32 NAR NASEG NASH. chunk_named RT AF GP arr (4 * cap) ARR ARSEG ARSH.
  chunk_named RT AF GP nad 32 NDR NDSEG NDSH. chunk_named RT AF GP arrd (4 * capd) ADR ADSEG ADSH.
  fframe_named RT AF fr 0%nat 64 nas 32 FCn FSn. fframe_named RT AF fr 0%nat 64 arr (4 * cap) FCa FSa.
  fframe_named RT AF fr 0%nat 64 nad 32 FCd FSd. fframe_named RT AF fr 0%nat 64 arrd (4 * capd) FCad FSad.
  lazymatch goal with A : ART RT Σi ?mm |- _ =>
    pose proof (proj2 (af_fshadow_apart RT AF Σi mm fr 0%nat A ltac:(rewrite FRSi; left; reflexivity)) fr 0%nat ltac:(rewrite FRSi; left; reflexivity)) as FSA;
    change (fs_size 0) with 64 in FSA; unfold shad, SHB in FSA end.
  destruct (u32arr_nth vals i ltac:(lia)) as (wi & Hwi).
  unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  unfold LSTK, STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  pose proof ST as (STa & STb & _).
  pose proof (agree_refl PF mc) as AGF.
  assert (PFS : forall a, PF a -> usp0 <= a \/ a < lo).
  { intros a [Ha _]. destruct (aclient_split RT AF Σi mc usp0 a ART0) as [H|H].
    { rewrite LVi, FRSi. apply (aclient_mono _ _ usp0 _ _ _ _ Ha); [unfold numa_live; intros e He; right; right; exact He| intros e He; exact He| clear; lia]. }
    { left; exact H. }
    { right. rewrite SPi in H. unfold STACK_WIN in H. clear - H LOW. lia. } }
  refresh RT AF. unfold shad, SHB in *. park_disj.
  unfold ext_shadow in FSH.
  local_acc FSH fr 6%nat 48 FR64 FR0 ACCv.
  (* [comment removed for export] *)
  walk_to AF MST [(usp0 - 16, usp0); (fr + 48, fr + 48 + 4)] [e_numaGetFValue].
  eapply evt_cut.
  { lazymatch goal with |- evt _ _ (MS _ ?F0 _ ?fc0 None ?mm _) =>
      eapply (numaGetFValue_evt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F0 fc0 mm usp0 lo L nas cap arr vals i (fr + 48) wi vl) end.
    all: lazymatch goal with
         | |- numa_obj _ _ _ _ _ _ => exact NOBJ
         | |- nth_error _ _ = _ => exact Hwi
         | |- acc _ _ _ _ => assumption
         | |- ro_cells _ _ _ _ => assumption
         | |- rw_cells _ _ _ _ => assumption
         | |- stk _ _ _ _ => assumption
         | |- mem_inv _ _ => assumption
         | |- _ mod _ = 0 => clear - FR64; Z.div_mod_to_equations; lia
         | |- _ => unfold parked, SEGTOP_A in *; clear - HI FR0 FR64 LOR SPT LOW SP0W NAR ARR FRHI FRSEG NASEG NASH ARSEG ARSH FRSH FCn FCa; lia
         end. }
  intros ms' PO. destruct PO as (b1 & b2 & b3 & b4 & b5 & b6 & b7 & F2 & m1 & -> & MUl & WMl & MIl & STl & CVL1 & EF2).
  lazymatch type of MUl with munch _ ?ma ?mb =>
    lazymatch goal with A : ART RT ?S ma |- _ =>
      loop_art RT AF S mb lo MUl ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac| exact I]]);
      loop_transport ma mb MUl ltac:(fun Hx => seg_side NAR ARR LOW LOR FRHI FR0 SP0W FRSEG FR64 FCn FCa FCd FCad FSA Hx);
      obj_fwd NOBJ MUl ltac:(fun b k a Hin Ha =>
        pose proof (live_apart_seg RT AF S ma fr 0%nat b k a A ltac:(rewrite FRSi; left; reflexivity) ltac:(rewrite LVi; right; right; exact Hin) Ha) as Hx;
        change (fs_size 0) with 64 in Hx; rewrite SPi in Hx; seg_side NAR ARR LOW LOR FRHI FR0 SP0W FRSEG FR64 FCn FCa FCd FCad FSA Hx);
      obj_fwd NOBJd MUl ltac:(fun b k a Hin Ha =>
        pose proof (live_apart_seg RT AF S ma fr 0%nat b k a A ltac:(rewrite FRSi; left; reflexivity) Hin Ha) as Hx;
        change (fs_size 0) with 64 in Hx; rewrite SPi in Hx; seg_side NAR ARR LOW LOR FRHI FR0 SP0W FRSEG FR64 FCn FCa FCd FCad FSA Hx) end end.
  fix_ret_pc. subst F2.
  agf_munch AGF MU ltac:(fun Hx => pose proof (PFS _ Hx) as HxS; destruct Hx as [_ HxO]; revert HxO HxS; clear - LOR; cbn [outside]; intros HxO HxS; repeat split; try exact I; lia).
  lazymatch goal with |- evt _ _ (MS _ ?FF _ _ _ _ _) => remember FF as F1 eqn:EF1; clear EF1 end.
  remember (nan_box (bv_extract 0 32 (le_bytes_to_word (le4 wi)))) as vw eqn:EVW. clear EVW.
  destruct DIR as [DIR|DIR]; subst dir.
  - (* [comment removed for export] *)
    awalk [0xee9f8; 0xeea40; 0xee9d0].
    step.
    lazymatch goal with |- evt _ _ (MS _ ?FF _ _ _ _ _) => remember FF as F2 eqn:EF2; clear EF2 end.
    step. step. step.
    fbr.
    + (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let v := eval vm_compute in c in change c with v; cbv iota end.
      step. step.
      cps_stop.
      lazymatch goal with |- cps _ (ASTA _ _ _ (eq (MS _ ?FF _ (frm_clear ?fcx) _ _ _))) _ =>
        eapply (TAIL Σi m1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FF fcx capd arrd i 1 vd vw) end.
      all: first [assumption | lia].
    + (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let v := eval vm_compute in c in change c with v; cbv iota end.
      step.
      lazymatch goal with |- evt _ _ (MS _ ?FF _ _ _ _ _) => remember FF as F3 eqn:EF3; clear EF3 end.
      step.
      lazymatch goal with |- evt _ _ (MS _ ?FF _ _ _ _ _) => remember FF as F4 eqn:EF4; clear EF4 end.
      step. step.
      fbr.
      2: { (* [comment removed for export] *)
        lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let v := eval vm_compute in c in change c with v; cbv iota end.
        cps_stop.
        lazymatch goal with |- cps _ (ASTA _ _ _ (eq (MS _ ?FF _ (frm_clear ?fcx) _ _ _))) _ =>
          eapply (TAIL Σi m1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FF fcx capd arrd loc 1 vd vw) end.
        all: first [assumption | lia]. }
      (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let v := eval vm_compute in c in change c with v; cbv iota end.
      step.
      awalk [e_numaAddNumber].
      at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac| exact I]])
                    ltac:(fun Hx => pose proof (PFS _ Hx) as HxS; destruct Hx as [_ HxO]; revert HxO HxS; clear - LOR; cbn [outside]; intros HxO HxS; repeat split; try exact I; lia).
      eapply cps_seq.
      { eapply (add_any RT AF NAF NA) with (lo := lo) (nad := nad) (capd := capd) (arrd := arrd) (vd := vd) (v := fcvt_s_w RNE (Z_to_bv 64 loc)) (L := L) (cr0 := cr0).
        all: lazymatch goal with
             | |- fdfs_only _ => exact FDO
             | |- mat_stable _ => exact MST
             | |- freg_is _ _ _ => unfold freg_is, fa0; apply freg_get_same; reflexivity
             | |- rt_live _ _ = _ => exact LVi
             | |- numa_obj _ _ _ _ _ _ => exact NOBJd
             | |- In _ CAPS => exact HCAP
             | |- lenv _ _ _ _ _ _ => lenv_tac
             | |- _ = _ => reflexivity
             | |- Z.of_nat (length (rt_frames _ _)) <= _ => rewrite FRSi; cbn [length]; clear - FRB; lia
             | |- forall _ _, _ => exact LVP
             | |- _ => first [assumption | clear - LVD HI VLEN CRi CR0 EGC LVB; lia]
             end. }
      after_call RT AF.
      lazymatch goal with AGx : agree_on (fun a => aclient _ _ _ a /\ _) ?ma ?mb |- _ =>
        obj_fwd_ag NOBJ AGx ltac:(fun b k a Hin Ha => split; [right; right; left; exists b, k; split; [exact Hin| lia]| exact I]) end.
      clear NOBJd.
      fold_ag ltac:(fun Hx => destruct Hx as [Hx _]; split; [rewrite FRSi; exact Hx| exact I]).
      lazymatch goal with H : rt_live RT ?S = numa_live nad ?c ?a L |- cps _ (ASTA RT ?S _ _) _ => rename H into LVn; rename S into Σn; rename c into capn; rename a into arrn end.
      lazymatch goal with H : numa_obj (rt_live RT Σn) _ nad capn arrn (vd ++ [?v]) |- _ => rename H into NOBJn end.
      lazymatch goal with H : In capn CAPS |- _ => rename H into HCAPn end.
      lazymatch goal with H : cr0 - ext_spent capn <= rt_credit RT Σn |- _ => rename H into CRn end.
      lazymatch goal with H : rt_frames RT Σn = rt_frames RT Σi |- _ => rewrite FRSi in H; rename H into FRSn end.
      lazymatch goal with H : rt_sp0 RT Σn = rt_sp0 RT Σi |- _ => rewrite SPi in H; rename H into SPn end.
      walk_to AF MST (@nil (Z * Z)) [0xeea34; 0xeea2c; 0xee9d0].
      step.
      lazymatch goal with |- evt _ _ (MS _ ?FF _ _ _ _ _) => remember FF as F5 eqn:EF5; clear EF5 end.
      awalk [0xee9d0].
      cps_stop.
      lazymatch goal with NO : numa_obj (rt_live RT Σn) ?mm nad capn arrn (vd ++ [?v]) |- cps _ (ASTA _ _ _ (eq (MS _ ?FF _ (frm_clear ?fcx) _ ?mm _))) _ =>
        eapply (TAIL Σn mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FF fcx capn arrn i (-1) (vd ++ [v]) vw) end.
      all: first [assumption | lia | rewrite length_app; cbn [length]; clear - LVD; lia].
  - (* [comment removed for export] *)
    awalk [0xee9f8; 0xeea40; 0xee9d0].
    step.
    lazymatch goal with |- evt _ _ (MS _ ?FF _ _ _ _ _) => remember FF as F2 eqn:EF2; clear EF2 end.
    step. step. step.
    fbr.
    + (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let v := eval vm_compute in c in change c with v; cbv iota end.
      step. step. step.
      cps_stop.
      lazymatch goal with |- cps _ (ASTA _ _ _ (eq (MS _ ?FF _ (frm_clear ?fcx) _ _ _))) _ =>
        eapply (TAIL Σi m1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FF fcx capd arrd i (-1) vd vw) end.
      all: first [assumption | lia].
    + (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let v := eval vm_compute in c in change c with v; cbv iota end.
      step.
      lazymatch goal with |- evt _ _ (MS _ ?FF _ _ _ _ _) => remember FF as F3 eqn:EF3; clear EF3 end.
      step.
      lazymatch goal with |- evt _ _ (MS _ ?FF _ _ _ _ _) => remember FF as F4 eqn:EF4; clear EF4 end.
      step. step.
      fbr.
      2: { (* [comment removed for export] *)
        lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let v := eval vm_compute in c in change c with v; cbv iota end.
        cps_stop.
        lazymatch goal with |- cps _ (ASTA _ _ _ (eq (MS _ ?FF _ (frm_clear ?fcx) _ _ _))) _ =>
          eapply (TAIL Σi m1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FF fcx capd arrd loc (-1) vd vw) end.
        all: first [assumption | lia]. }
      (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let v := eval vm_compute in c in change c with v; cbv iota end.
      step.
      awalk [e_numaAddNumber].
      at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac| exact I]])
                    ltac:(fun Hx => pose proof (PFS _ Hx) as HxS; destruct Hx as [_ HxO]; revert HxO HxS; clear - LOR; cbn [outside]; intros HxO HxS; repeat split; try exact I; lia).
      eapply cps_seq.
      { eapply (add_any RT AF NAF NA) with (lo := lo) (nad := nad) (capd := capd) (arrd := arrd) (vd := vd) (v := fcvt_s_w RNE (Z_to_bv 64 loc)) (L := L) (cr0 := cr0).
        all: lazymatch goal with
             | |- fdfs_only _ => exact FDO
             | |- mat_stable _ => exact MST
             | |- freg_is _ _ _ => unfold freg_is, fa0; apply freg_get_same; reflexivity
             | |- rt_live _ _ = _ => exact LVi
             | |- numa_obj _ _ _ _ _ _ => exact NOBJd
             | |- In _ CAPS => exact HCAP
             | |- lenv _ _ _ _ _ _ => lenv_tac
             | |- _ = _ => reflexivity
             | |- Z.of_nat (length (rt_frames _ _)) <= _ => rewrite FRSi; cbn [length]; clear - FRB; lia
             | |- forall _ _, _ => exact LVP
             | |- _ => first [assumption | clear - LVD HI VLEN CRi CR0 EGC LVB; lia]
             end. }
      after_call RT AF.
      lazymatch goal with AGx : agree_on (fun a => aclient _ _ _ a /\ _) ?ma ?mb |- _ =>
        obj_fwd_ag NOBJ AGx ltac:(fun b k a Hin Ha => split; [right; right; left; exists b, k; split; [exact Hin| lia]| exact I]) end.
      clear NOBJd.
      fold_ag ltac:(fun Hx => destruct Hx as [Hx _]; split; [rewrite FRSi; exact Hx| exact I]).
      lazymatch goal with H : rt_live RT ?S = numa_live nad ?c ?a L |- cps _ (ASTA RT ?S _ _) _ => rename H into LVn; rename S into Σn; rename c into capn; rename a into arrn end.
      lazymatch goal with H : numa_obj (rt_live RT Σn) _ nad capn arrn (vd ++ [?v]) |- _ => rename H into NOBJn end.
      lazymatch goal with H : In capn CAPS |- _ => rename H into HCAPn end.
      lazymatch goal with H : cr0 - ext_spent capn <= rt_credit RT Σn |- _ => rename H into CRn end.
      lazymatch goal with H : rt_frames RT Σn = rt_frames RT Σi |- _ => rewrite FRSi in H; rename H into FRSn end.
      lazymatch goal with H : rt_sp0 RT Σn = rt_sp0 RT Σi |- _ => rewrite SPi in H; rename H into SPn end.
      walk_to AF MST (@nil (Z * Z)) [0xeea88; 0xeea80; 0xee9d0].
      step.
      lazymatch goal with |- evt _ _ (MS _ ?FF _ _ _ _ _) => remember FF as F5 eqn:EF5; clear EF5 end.
      awalk [0xee9d0].
      cps_stop.
      lazymatch goal with NO : numa_obj (rt_live RT Σn) ?mm nad capn arrn (vd ++ [?v]) |- cps _ (ASTA _ _ _ (eq (MS _ ?FF _ (frm_clear ?fcx) _ ?mm _))) _ =>
        eapply (TAIL Σn mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FF fcx capn arrn i 1 (vd ++ [v]) vw) end.
      all: first [assumption | lia | rewrite length_app; cbn [length]; clear - LVD; lia].
Qed.
End SWEEP.
