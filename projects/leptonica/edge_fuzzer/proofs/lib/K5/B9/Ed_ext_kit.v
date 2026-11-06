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
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.B9 Require Import Layout.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.B9 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit D_iface D_defs Lept_kit Lept_iface Lept_env LeptC_kit Lept_objkit LeptL_kit Ed_fp Ed_iface Numa_kit Ed_ext_defs.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Ltac chunk_named RT AF GP p n R1 R2 R3 :=
  match goal with
  | A : ART RT ?S ?mm |- _ =>
      let IN := fresh "IN" in
      assert (IN : In (p, n) (rt_live RT S)) by (solve [in_live_tac]);
      pose proof (af_live_range RT AF S mm p n A IN) as (_ & R1 & R2);
      pose proof (gp_live_hi RT GP S mm p n A IN) as R3;
      unfold STACK_WIN, SEGTOP_A in R1, R2;
      repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H in R1 end; clear IN
  end.
Ltac fframe_named RT AF fr k SZ p n D1 D2 :=
  match goal with
  | A : ART RT ?S ?mm, FRS : rt_frames RT ?S = (fr, k) :: _ |- _ =>
      let IN := fresh "IN" in
      assert (IN : In (p, n) (rt_live RT S)) by (solve [in_live_tac]);
      pose proof (af_frames_range RT AF S mm fr k A ltac:(rewrite FRS; left; reflexivity)) as (_ & _ & _ & D1);
      specialize (D1 p n IN);
      pose proof (af_fshadow_apart RT AF S mm fr k A ltac:(rewrite FRS; left; reflexivity)) as (D2 & _);
      specialize (D2 p n IN);
      change (fs_size k) with SZ in D1, D2; unfold shad, SHB in D2; clear IN
  end.

(* [comment removed for export] *)
Ltac seg_side NAR ARR LOW LOR FRHI FR0 SP0W FRSEG FR64 FCD FCD0 FCD1 FCD2 FSA Hx :=
  repeat match goal with H : rt_sp0 _ _ = rt_sp0 _ _ |- _ => rewrite H in Hx end;
  cbn [outside]; unfold parked, shad, SHB, STACK_WIN, SEGTOP_A in *; clear - Hx NAR ARR LOW LOR FRHI FR0 SP0W FRSEG FR64 FCD FCD0 FCD1 FCD2 FSA;
  repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia].

(* [comment removed for export] *)
Ltac obj_fwd NOBJ MU apart :=
  lazymatch type of MU with munch ?W ?ma ?mb =>
  lazymatch type of NOBJ with numa_obj ?lv ma ?na ?c ?ar ?vs =>
    apply (numa_obj_keep lv ma mb na c ar vs) in NOBJ;
    [| apply (keeps_live_of_munch lv W ma mb MU);
       let b := fresh "b" in let k := fresh "k" in let a := fresh "a" in let Hin := fresh "Hin" in let Ha := fresh "Ha" in
       intros b k a Hin Ha; apart b k a Hin Ha ]
  end end.
(* [comment removed for export] *)
Ltac obj_fwd_ag NOBJ AG inP :=
  lazymatch type of AG with agree_on ?P ?ma ?mb =>
  lazymatch type of NOBJ with numa_obj ?lv ma ?na ?c ?ar ?vs =>
    apply (numa_obj_keep lv ma mb na c ar vs) in NOBJ;
    [| apply (keeps_live_of_agree lv P ma mb AG);
       let b := fresh "b" in let k := fresh "k" in let a := fresh "a" in let Hin := fresh "Hin" in let Ha := fresh "Ha" in
       intros b k a Hin Ha; inP b k a Hin Ha ]
  end end.

Section ExtKit.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.

(* [comment removed for export] *)
Lemma ext_chunk_apart : forall Σ' (m : mem) l1 p n l2 live0 frs usp a,
  ART RT Σ' m -> rt_live RT Σ' = l1 ++ (p, n) :: l2 -> (forall e, In e live0 -> In e (l1 ++ l2)) -> rt_frames RT Σ' = frs ->
  rt_sp0 RT Σ' - STACK_WIN <= usp ->
  aclient live0 frs usp a -> a < p \/ p + n <= a.
Proof using AF.
  intros Σ' m l1 p n l2 live0 frs usp a HA LV SUB FRS SPL Ha.
  assert (INL : In (p, n) (rt_live RT Σ')) by (rewrite LV; apply in_or_app; right; left; reflexivity).
  pose proof (af_live_range RT AF Σ' m p n HA INL) as (P0 & PHI & PSEG).
  unfold STACK_WIN, USTACK_TOP, SEGTOP_A in *.
  destruct Ha as [H|[H|[H|[H|H]]]].
  - right. lia.
  - pose proof (client_static_below a H) as HB. unfold SEGTOP_A in HB.
    destruct H as ((l & h & Hin & Hx) & _). unfold CLIENT_STATIC in Hin. cbn [In] in Hin.
    assert (X : 0x10000 <= a) by (repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
    lia.
  - destruct H as (p' & n' & Hin & Hp).
    pose proof (af_live_disj RT AF Σ' m p n p' n' l1 l2 HA LV (SUB _ Hin)) as D. lia.
  - destruct H as (f & k & Hin & Hf). rewrite <- FRS in Hin.
    pose proof (af_frames_range RT AF Σ' m f k HA Hin) as (_ & _ & _ & FLV). specialize (FLV p n INL). lia.
  - destruct H as (f & k & Hin & Hf). rewrite <- FRS in Hin.
    pose proof (af_fshadow_apart RT AF Σ' m f k HA Hin) as (SA1 & _). specialize (SA1 p n INL). lia.
Qed.

Hypothesis NAF : numaAddNumber_fast_cps RT.
Hypothesis NA : numaAddNumber_cps RT.

Lemma add_any : forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (nad capd arrd : Z) (vd : list word) (v : word) (L : list (Z * Z)) (cr0 : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 nad -> freg_is F fa0 v ->
  rt_live RT Σ = numa_live nad capd arrd L ->
  numa_obj (rt_live RT Σ) m nad capd arrd vd ->
  In capd CAPS -> Z.of_nat (length vd) < 20000 ->
  cr0 - ext_spent capd <= rt_credit RT Σ -> EXTREMA_GROWTH_COST <= cr0 ->
  lenv RT Σ m sp lo (LSTK 5) ->
  Z.of_nat (length (rt_frames RT Σ)) <= Z.of_nat FRAMES_MAX -> Z.of_nat (length L) + 3 <= LIVE_MAX -> (forall p n, In (p, n) L -> 0 < n) ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_numaAddNumber m)))
    (fun c => exists (Σ' : rts RT) (capd' arrd' : Z) (v' : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) m' ms
          /\ lpost_f RT Σ Σ' m m' sp lo
          /\ keepsL RT L Σ sp [] m m'
          /\ numa_obj (rt_live RT Σ') m' nad capd' arrd' (vd ++ [v'])) c
       /\ rt_live RT Σ' = numa_live nad capd' arrd' L /\ In capd' CAPS /\ cr0 - ext_spent capd' <= rt_credit RT Σ'
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ).
Proof using AF NAF NA.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo nad capd arrd vd v L cr0
    FDO MST TP A0 FV LV NOBJ HCAP VDL CR CR0 ENV FRB LVB LVP.
  pose proof (caps_facts capd HCAP) as (CAPB & CAP2 & CAPC). pose proof EGC_val as EGC.
  pose proof (numa_obj_facts _ _ _ _ _ _ NOBJ) as (LEND & _ & ND0 & ND16 & AD0 & AD16 & INd & INad & NEd).
  pose proof ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  assert (LVPS : forall p n, In (p, n) (rt_live RT Σ) -> 0 < n).
  { intros p n H. rewrite LV in H. unfold numa_live in H. cbn [In] in H.
    destruct H as [H|[H|H]]; [injection H; intros; subst; lia| injection H; intros; subst; lia| exact (LVP p n H)]. }
  assert (KEEP1 : forall a, aclient L (rt_frames RT Σ) (bv_unsigned sp) a -> a < nad \/ nad + 32 <= a).
  { intros a Ha. apply (ext_chunk_apart Σ m [(arrd, 4 * capd)] nad 32 L L (rt_frames RT Σ) (bv_unsigned sp) a ART0); [exact LV| intros e He; right; exact He| reflexivity| unfold LSTK, RT_STACK in LOR; lia| exact Ha]. }
  assert (KEEP2 : forall a, aclient L (rt_frames RT Σ) (bv_unsigned sp) a -> a < arrd \/ arrd + 4 * capd <= a).
  { intros a Ha. apply (ext_chunk_apart Σ m [] arrd (4 * capd) ((nad, 32) :: L) L (rt_frames RT Σ) (bv_unsigned sp) a ART0); [exact LV| intros e He; right; exact He| reflexivity| unfold LSTK, RT_STACK in LOR; lia| exact Ha]. }
  assert (SUBL : forall a, aclient L (rt_frames RT Σ) (bv_unsigned sp) a -> aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) a).
  { intros a Ha. apply (aclient_mono _ _ (bv_unsigned sp) _ _ _ _ Ha); [intros e He; rewrite LV; right; right; exact He| intros e He; exact He| lia]. }
  destruct (Z_lt_le_dec (Z.of_nat (length vd)) capd) as [FAST|GROW].
  - (* [comment removed for export] *)
    eapply cps_conseq; [ | intros c Hc; exact Hc | ].
    + eapply (NAF Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo nad capd arrd vd v);
        [exact FDO| exact MST| exact TP| exact A0| exact FV| exact NOBJ| exact FAST| exact ENV|].
      unfold lres. rewrite LV. unfold numa_live. cbn [length]. unfold LIVE_MAX in *.
      split; [lia|]. split; [lia|]. split; [pose proof (ext_spent_le capd); lia|].
      intros p n H. apply (LVPS p n). rewrite LV. exact H.
    + intros c (Σ' & HA & LV' & FRS' & SP' & CR').
      exists Σ', capd, arrd, v.
      split.
      2: { split; [rewrite LV'; exact LV|]. split; [exact HCAP|]. split; [lia|]. split; [exact FRS'| exact SP']. }
      eapply (ASTA_conseq RT); [exact HA|]. cbv beta. intros ms (m' & RS & LP & KP & NO).
      exists m'. split; [exact RS|].
      split. { destruct LP as (RA & LH' & SSP'). split; [exact (rt_after_f_of RT Σ' _ _ _ _ RA)| split; assumption]. }
      split; [| exact NO].
      unfold keeps, keepsL in *. intros a Ha Ho. apply KP.
      { rewrite LV'. apply SUBL. exact Ha. }
      { cbn [outside]. pose proof (KEEP1 _ Ha). pose proof (KEEP2 _ Ha). repeat split; try exact I; lia. }
  - (* [comment removed for export] *)
    assert (EQL : Z.of_nat (length vd) = capd) by lia.
    assert (C12 : capd <= 12800). { destruct (Z_le_gt_dec capd 12800) as [H|H]; [exact H|]. pose proof (caps_12800 capd HCAP ltac:(lia)). lia. }
    pose proof (CAP2 C12) as HCAP2. pose proof (ext_spent_grow capd HCAP C12) as SPG.
    assert (SP0 : ext_spent capd = 0) by (unfold ext_spent; destruct (Z.leb_spec capd 12800); [reflexivity| lia]).
    pose proof (ext_spent_le (2 * capd)) as SPL.
    eapply cps_conseq; [ | intros c Hc; exact Hc | ].
    + eapply (NA Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo nad capd arrd vd v);
        [exact FDO| exact MST| exact TP| exact A0| exact FV| exact NOBJ| lia| exact ENV|].
      unfold lres. rewrite LV. unfold numa_live. cbn [length]. unfold LIVE_MAX in *.
      split; [lia|]. split; [lia|]. split; [lia|].
      intros p n H. apply (LVPS p n). rewrite LV. exact H.
    + intros c (Σ' & cap' & arr' & v' & HA & DISJ & FRS' & SP' & CR').
      destruct DISJ as [(LT & _)|(_ & EC & LV')]; [exfalso; lia|].
      exists Σ', (2 * capd), arr', v'. subst cap'.
      assert (LRM : live_remove arrd (rt_live RT Σ) = (nad, 32) :: L).
      { rewrite LV. unfold numa_live. rewrite lrm_cons. cbn [fst]. rewrite Z.eqb_refl. apply lrm_notin.
        apply (live_head_notin RT AF Σ m arrd (4 * capd) ((nad, 32) :: L) ART0 LV ltac:(lia)).
        intros e He. destruct He as [<-|He]; [cbn; lia| destruct e as [p n]; exact (LVP p n He)]. }
      split.
      2: { split; [rewrite LV', LRM; reflexivity|]. split; [exact HCAP2|]. split; [lia|]. split; assumption. }
      eapply (ASTA_conseq RT); [exact HA|]. cbv beta. intros ms (m' & RS & LP & KP & NO).
      exists m'. split; [exact RS|]. split; [exact LP|]. split; [| exact NO].
      unfold keepsL in *. rewrite LRM in KP. intros a Ha Ho. apply KP.
      { apply (aclient_mono _ _ (bv_unsigned sp) _ _ _ _ Ha); [intros e He; right; exact He| intros e He; exact He| lia]. }
      { cbn [outside]. pose proof (KEEP1 _ Ha). repeat split; try exact I; lia. }
Qed.
End ExtKit.
