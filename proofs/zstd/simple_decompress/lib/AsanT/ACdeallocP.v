(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import MM_syscalls WStr.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import SysStepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg AProto ABase AKit AKit2 AKitQ AKitR ABytes AQConst AModelFacts ARep ARepKit ARepFrame ALayout AHeapP
     ARepQ ARepQP ARepQR AFreeRep AFreeGeo AFreeRead ARecRep ARepQD ARefillP RT_stubs
     F_apoison F_acache F_aalloc3 F_ammap F_aensure F_apopulate F_agetfrom F_arefill F_amaybe F_areturn F_acdrain F_acdealloc F_arecyc1 ARecyc1P.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import LiaTier0U.
Local Ltac Stdlib.micromega.Lia.lia ::= lia_tier0u.
Local Ltac OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib.StoreFast.tlia ::= tlia_u.
Local Ltac OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib.StoreFast.lia3 ::= lia3_u.
Import ListNotations.
Import Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Notation Wk0 sp t CA FA nf mfa' SHF0 SHF1 RI :=
  ([(sp - 688, sp); (t + 2784, t + 2792); (t + 2800, t + 3168);
    (CA, CA + 4); (CA + 16, CA + 80); (FA + 4 * nf, FA + mfa'); (SHF0, SHF1); (RI, RI + 8); (RI + 16, RI + 32); (RI + 72, RI + 128)]%Z) (only parsing).

(* [comment removed for export] *)
Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6443008 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma ablk_int {rc : runConstT} : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6443008 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Ltac band_int H :=
  let k := fresh "k" H in let A := fresh "KA" H in let B := fresh "KB" H in let C := fresh "KC" H in let D := fresh "KD" H in
  let G1 := fresh "G" in let G2 := fresh "G" in
  lazymatch type of H with
  | sclr ?a ?n =>
      assert (G1 : 0 <= a) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia); assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (sclr_int a n H G1 G2) as (k & A & B & C); clear G1 G2
  | iclr ?a ?n =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | 4096 <= ?a /\ (?a + ?n <= _ \/ _ <= ?a) =>      (* [comment removed for export] *)
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | ablk ?lo ?hi => let E := fresh "KE" H in destruct (ablk_int lo hi H) as (k & A & B & E & C & D)
  end.

Section CANSEC1. Context {rc : runConstT}.
Section Kinds0.
Variables (sp lo t ctx SB c RB FA RI CA mu au nf mfa mfa' SHF0 SHF1 : Z).
Definition reckf0 : Prop :=
     (ATOP <= lo /\ lo <= sp - 688 /\ sp <= 2^64)
  /\ (sclr t 4096 /\ iclr t 4096 /\ t + 4096 <= ATOP /\ sclr ctx 65536 /\ 6443008 <= ctx /\ ctx + 65536 <= ATOP /\ (ctx + 4096 <= t \/ t + 4096 <= ctx))
  /\ (1 <= c <= 31 /\ CA = t + 208 + c * 80)
  /\ (17594333495296 <= SB /\ SB + 137438957568 <= ATOP /\ RB = SB + c * 4294967296 /\ FA = RB + 3758096384 /\ RI = SB + 137438953472 + c * 128)
  /\ (t + 4096 <= SB \/ SB + 137438957568 <= t) /\ (ctx + 65536 <= SB \/ SB + 137438957568 <= ctx)
  /\ (0 <= au /\ au <= mu /\ mu <= 3758096384 /\ 0 <= nf /\ 4 * nf <= mfa /\ mfa <= mfa' /\ mfa' <= 536870912)
  /\ (2201439137792 <= SHF0 /\ SHF0 <= SHF1 /\ SHF1 <= 17594333495296).
Hypothesis KF : reckf0.

Ltac kind0 := pose proof KF as KF'; unfold reckf0, AIMG_HI in *;
  destruct KF' as (F_lo & (Ft1 & Ft2 & Ft3 & Fc1 & Fc2 & Fc3 & Ftc) & F_c & F_sb & F_tsb & F_csb & F_mu & F_sh);
  band_int Ft2; band_int Ft1; band_int Fc1; clear Ft1 Ft2 Fc1;   (* [comment removed for export] *)
  cbn [disjoint_from]; repeat (split; [lia|]); first [lia | exact I].

Lemma RK0_img : forall A k, 65536 <= A -> 0 <= k -> A + k <= 6443008 -> disjoint_from (Wk0 sp t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind0. Qed.
Lemma RK0_obj : forall A k, ((6443008 <= A /\ A + k <= 2147446784) \/ 17594333495296 <= A) -> A + k <= ATOP -> 0 <= k ->      (* [comment removed for export] *)
  (A + k <= t \/ t + 4096 <= A) -> (A + k <= SB \/ SB + 137438957568 <= A) ->
  disjoint_from (Wk0 sp t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind0. Qed.
Lemma RK0_tlow : forall A k, t <= A -> A + k <= t + 288 -> 0 <= k -> disjoint_from (Wk0 sp t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind0. Qed.
Lemma RK0_thigh : forall A k, t + 3168 <= A -> A + k <= t + 4096 -> 0 <= k -> disjoint_from (Wk0 sp t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind0. Qed.
Lemma RK0_tstat : forall A k, t + 2768 <= A -> A + k <= t + 2800 -> 0 <= k -> (A + k <= t + 2784 \/ t + 2792 <= A) ->
  disjoint_from (Wk0 sp t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind0. Qed.
Lemma RK0_rec : forall A k, t + 288 <= A -> A + k <= t + 2768 -> 0 <= k -> (A + k <= CA \/ CA + 4 <= A) -> (A + k <= CA + 16 \/ CA + 80 <= A) ->
  disjoint_from (Wk0 sp t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind0. Qed.
Lemma RK0_reg_other : forall A k, SB <= A -> 0 <= k -> (A + k <= RB \/ RB + 4294967296 <= A) -> A + k <= SB + 137438953472 ->
  disjoint_from (Wk0 sp t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind0. Qed.
(* [comment removed for export] *)
Lemma RK0_space_c : forall A k, RB <= A -> A + k <= RB + mu -> 0 <= k ->
  disjoint_from (Wk0 sp t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind0. Qed.
Lemma RK0_gap : forall A k, RB + mu <= A -> A + k <= FA + 4 * nf -> 0 <= k -> disjoint_from (Wk0 sp t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind0. Qed.
Lemma RK0_ri : forall A k, SB + 137438953472 <= A -> A + k <= SB + 137438957568 -> 0 <= k ->
  (A + k <= RI \/ RI + 8 <= A) -> (A + k <= RI + 16 \/ RI + 32 <= A) -> (A + k <= RI + 72 \/ RI + 128 <= A) ->
  disjoint_from (Wk0 sp t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind0. Qed.
Lemma RK0_sh : forall A k, 2201439137792 <= A -> A + k <= 17594333495296 -> 0 <= k ->
  (A + k <= SHF0 \/ SHF1 <= A) ->
  disjoint_from (Wk0 sp t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind0. Qed.
Lemma RK0_stkhi : forall A k, sp <= A -> 0 <= k -> disjoint_from (Wk0 sp t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind0. Qed.
End Kinds0.


Lemma repeat_app3 : forall {X} (x : X) a b c, repeat x a ++ repeat x b ++ repeat x c = repeat x (a + b + c).
Proof. intros. rewrite !repeat_app. rewrite app_assoc. reflexivity. Qed.

(* [comment removed for export] *)
Lemma AQdr_unbatch : forall R L st X m kb nb b1 ctx l1 l2 drained,
  AQdr R 0 0 L st X m -> qr_pendb R = [kb] -> qr_pend R = [] ->
  x_busy X = l1 ++ bany BBatch K_BATCH_CLASS kb nb b1 ctx :: l2 -> awf L st X ->
  AQdr (qr_unbatch R) 0 0 L st (xrec st X K_BATCH_CLASS kb l1 l2 drained) m.
Proof.
  intros R L st X m kb nb b1 ctx l1 l2 drained (QC & MX & TC & GL & TB & IA & CP & NUM & NT) EB EP XB WF.
  unfold AQdr, qr_unbatch. cbn [qr_loc qr_glob qr_tmp qr_ia].
  split; [exact QC|]. split; [exact MX|]. split; [exact TC|]. split; [exact GL|]. split; [exact TB|]. split; [exact IA|].
  split; [| exact (conj NUM NT)].
  exact (qcoupled_rec_unbatch L st st X R kb nb b1 ctx l1 l2 drained CP EB EP XB WF eq_refl eq_refl).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section P.
Variables (ASECc : list achunk -> alayout -> astate -> aconc -> amem -> Prop)
          (AD : alayout -> amem -> Prop) (AF : alayout -> list ablock -> amem -> Prop).
Let AHr := AHr ASECc AD AF.
Hypothesis HL : forall R cs, ahole_laws (AHr R cs).

(* [comment removed for export] *)
Definition acd24_ret (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : astate) (X : aconc) (R : qrconc) (cs : list achunk) (lo : Z) (m : amem)
    (stX : astate) (X' : aconc) (RNG' : footprint) (ms' : machine_state) : Prop :=
  let c := K_BATCH_CLASS in
  fp_le RNG RNG' /\ exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (mfa' : Z),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch (cd_W L (bv_unsigned sp) c (c_num_freed (get_cls st c)) (c_mapped_free_array (get_cls st c)) mfa') m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ c_mapped_free_array (get_cls st c) <= mfa' <= K_FREEARR_MAX
    /\ AREP (AHr (qr_unbatch R) cs) L stX X' m' /\ arng L RNG' stX
    /\ a_cinit stX = true /\ a_live stX = a_live st /\ a_next stX = a_next st
    /\ a_qloc stX = a_qloc st /\ a_qloc_bytes stX = a_qloc_bytes st /\ a_qglob stX = a_qglob st /\ a_qglob_bytes stX = a_qglob_bytes st
    /\ a_nsec stX = a_nsec st /\ a_nres stX = a_nres st /\ a_ptr_array stX = a_ptr_array st /\ a_space_beg stX = a_space_beg st
    /\ (forall c', c' <> c -> get_cls stX c' = get_cls st c')
    /\ (forall b, In b (x_busy X') -> In b (x_busy X))
    /\ (forall b p, In b (x_busy X) -> xb_st b = BLive p -> In b (x_busy X')).

Definition store_cd24_stmt : Prop :=
  forall (L : alayout) (RNG RNG' : footprint) (sp : word) (m m' : amem) (st stX : astate) (X : aconc) (R : qrconc)
         (cs : list achunk) (kb nb b1 ctx lo : Z) (l1 l2 : list xbusy) (tail : list word),
  let c := K_BATCH_CLASS in
  alayout_ok L -> arng L RNG st -> AREP (AHr R cs) L st X m ->
  qr_pendb R = [kb] -> qr_pend R = [] -> x_busy X = l1 ++ bany BBatch K_BATCH_CLASS kb nb b1 ctx :: l2 ->
  ATOP <= lo -> lo <= bv_unsigned sp - 688 ->
  u32arr bsegs m (acache_addr L c + 16) (map (fun k => Z_to_bv 64 (acompact c k)) (xc_cache (x_cls X c)) ++ tail) ->
  (length (xc_cache (x_cls X c)) + length tail = 16)%nat ->
  cdealloc_ret L RNG sp st c (abatch_addr L kb) lo (map (fun k => Z_to_bv 64 (acompact c k)) (xc_cache (x_cls X c)) ++ tail) m stX RNG' m' ->
  exists X' mfa',
       munch (cd_W L (bv_unsigned sp) c (c_num_freed (get_cls st c)) (c_mapped_free_array (get_cls st c)) mfa') m m'
    /\ wmono bsegs m m'
    /\ c_mapped_free_array (get_cls st c) <= mfa' <= K_FREEARR_MAX
    /\ AREP (AHr (qr_unbatch R) cs) L stX X' m' /\ arng L RNG' stX
    /\ a_cinit stX = true /\ a_live stX = a_live st /\ a_next stX = a_next st
    /\ a_qloc stX = a_qloc st /\ a_qloc_bytes stX = a_qloc_bytes st /\ a_qglob stX = a_qglob st /\ a_qglob_bytes stX = a_qglob_bytes st
    /\ a_nsec stX = a_nsec st /\ a_nres stX = a_nres st /\ a_ptr_array stX = a_ptr_array st /\ a_space_beg stX = a_space_beg st
    /\ (forall c', c' <> c -> get_cls stX c' = get_cls st c')
    /\ (forall b, In b (x_busy X') -> In b (x_busy X))
    /\ (forall b p, In b (x_busy X) -> xb_st b = BLive p -> In b (x_busy X')).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma cd24_store : store_cd24_stmt.
Proof.
  unfold store_cd24_stmt.
  intros L RNG RNG' sp m m' st stX X R cs kb nb b1 ctx lo l1 l2 tail ALO ARNG AR EB EP XB CEIL LO CH LCH CDR.
  set (c := K_BATCH_CLASS) in *. set (k := kb) in *.
  (* [comment removed for export] *)
  pose proof AR as AR0. destruct AR0 as (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & RT2 & AVL & RT3).
  cbn [ah_quar ah_sec ah_depot AHr] in HQ, HS, HD.
  destruct THR as (T0c & T40 & CACHES & CSTATS & [sj [STATS LSJ]] & UNW).
  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  destruct (any_range L st X BBatch c k nb b1 ctx l1 l2 XB WF) as [HC KR].
  destruct (PERC c HC) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & LENF & LENC & CNTB & ND & RANGE).
  destruct (CLS c HC) as (RCELLS & FARR & SLOTS & SSH). destruct (AVL c HC) as [AZU AZF].
  destruct RCELLS as (MTX16 & REG & RJ4 & EXH & RJ56). destruct FARR as (FL & FJ & FSJ).
  pose proof SLOTS as SLOTS0. pose proof SSH as SSH0. destruct SLOTS as [SL UND]. destruct SSH as [SSL SUND].
  pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & SP4).
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4).
  pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5).
  pose proof TL1 as TL1u. pose proof TL4 as TL4u. pose proof CL1 as CL1u. unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in TL1u, TL4u, CL1u.   (* [comment removed for export] *)
  pose proof (alayout_res_disj L ALO) as [SCX TSP].
  pose proof (size_of_class_facts c HC) as [SZ16 SZM].
  pose proof (ARecRep.max_cached_range c) as (MCR & MCH & MCE).
  (* [comment removed for export] *)
  destruct CDR as (FPLE & drained & mfa' & sj' & sta' & DR & GCX & STE & MFD & NEWB & NEWM & NEWMOD & MU2 & WM2 & MI' & ST' & RECS' & RECc' & CH' & MTX' & REG' & J72' & STATS' & LSJ' & STA' & DRA & FJ' & AZF' & MC').
  unfold K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN in *.
  change (2^37) with 137438953472 in *.
  (* [comment removed for export] *)
  set (S := size_of_class c) in *. set (half := max_cached c / 2) in *.
  set (mu := c_mapped_user (get_cls st c)) in *. set (au := c_allocated_user (get_cls st c)) in *.
  set (nf := c_num_freed (get_cls st c)) in *. set (mfa := c_mapped_free_array (get_cls st c)) in *. set (cnt := c_count (get_cls st c)) in *.
  set (nd := ndist st c) in *.
  set (nf' := if drained then nf + half else nf) in *. set (cnt' := if drained then cnt - half + 1 else cnt + 1) in *.
  set (X' := xrec st X c k l1 l2 drained).
  set (AB := aslot_addr L c k) in *.
  assert (GEO : aregion_info L c = al_space_beg L + 137438953472 + c * 128 /\ aregion L c = al_space_beg L + c * 4294967296
                /\ afreearr L c = al_space_beg L + c * 4294967296 + 3758096384 /\ acache_addr L c = al_t L + 208 + c * 80).
  { unfold aregion_info, afreearr, aregion, acache_addr, K_REGION, K_FREEARR_OFF, K_SPACE_SIZE, ARI_STRIDE. change (2^32) with 4294967296. change (2^37) with 137438953472. repeat split; reflexivity. }
  destruct GEO as (RIE & RBE & FAE & CAE).
  set (RB := aregion L c) in *. set (FA := afreearr L c) in *. set (RI := aregion_info L c) in *. set (CA := acache_addr L c) in *.
  (* [comment removed for export] *)
  assert (MCle : forall c', max_count st c' <= max_cached c') by (intros c'; unfold max_count; pose proof (ARecRep.max_cached_range c'); destruct (a_cinit st); lia).
  assert (DRC : if drained then cnt = max_cached c else cnt < max_cached c).
  { rewrite DR. pose proof (MCle c) as M. unfold max_count in CNTB, M. fold cnt in CNTB.
    destruct (a_cinit st); cbn [andb]; [destruct (Z.eqb_spec cnt (max_cached c)); [exact e| lia] | lia]. }
  assert (HALF : 1 <= half <= 8 /\ max_cached c = 2 * half) by (subst half; clear -MCR MCH MCE; lia). destruct HALF as [HALF MC2].
  assert (CNT16 : 0 <= cnt <= 16 /\ cnt' - 1 <= cnt /\ 1 <= cnt' <= 16 /\ Z.of_nat (length (xc_cache (x_cls X c))) = cnt /\ nf <= nf' <= nf + 8).
  { subst cnt' nf'. fold cnt in CNTB, LENC. pose proof (MCle c). destruct drained; clear -CNTB LENC DRC HALF MC2 MCR H; lia. }
  destruct CNT16 as (CNT16 & CNTle & CNT1 & LENCc & NFle).
  (* [comment removed for export] *)
  set (st_r := put_cls c (mkAClass mu au nf' mfa' cnt') (init_cache st)) in *.
  assert (STR : stX = st_r) by (rewrite STE, GCX; reflexivity). subst stX.
  pose proof (init_cache_fields st) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11).
  assert (GR : get_cls st_r c = mkAClass mu au nf' mfa' cnt') by (subst st_r; apply get_cls_put_cls_eq).
  assert (GO : forall c', c' <> c -> get_cls st_r c' = get_cls st c') by (intros c' NE; subst st_r; rewrite (get_cls_put_cls_ne c c') by exact NE; apply init_cache_cls).
  assert (CIR : a_cinit st_r = true) by (subst st_r; cbn; exact E11).
  assert (NDR : ndist st_r c = nd) by (unfold ndist; rewrite GR; reflexivity).
  assert (EF : a_live st_r = a_live st /\ a_next st_r = a_next st /\ a_qloc st_r = a_qloc st /\ a_qloc_bytes st_r = a_qloc_bytes st
               /\ a_qglob st_r = a_qglob st /\ a_qglob_bytes st_r = a_qglob_bytes st /\ a_nsec st_r = a_nsec st /\ a_nres st_r = a_nres st
               /\ a_ptr_array st_r = a_ptr_array st /\ a_space_beg st_r = a_space_beg st).
  { subst st_r. destruct (put_cls_fields c (mkAClass mu au nf' mfa' cnt') (init_cache st)) as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & _).
    rewrite P1, P2, P3, P4, P5, P6, P7, P8, P9, P10, E1, E2, E3, E4, E5, E6, E7, E8, E9, E10. repeat split; reflexivity. }
  destruct EF as (EF1 & EF2 & EF3 & EF4 & EF5 & EF6 & EF7 & EF8 & EF9 & EF10).
  (* [comment removed for export] *)
  pose proof (slot_geo L st X c k ALO WF HC KR) as (_ & _ & AL16 & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & R8 & M8).
  fold S AB RB mu au in AL16, G1, G2, G3, G4, G5, G6, G7, G8, R8, M8.
  (* [comment removed for export] *)
  assert (AU8 : au mod 8 = 0).
  { pose proof (proj2 (Z.div_exact au S ltac:(clear -SZ16; lia)) A3) as EA. pose proof (proj2 (Z.div_exact S 16 ltac:(clear; lia)) SZM) as ES.
    rewrite ES in EA at 1. rewrite EA. replace (16 * (S / 16) * (au / S)) with ((2 * (S / 16) * (au / S)) * 8) by (clear; lia). apply Z_mod_mult. }
  set (SHF0 := shad (FA + mfa)) in *. set (SHF1 := SHF0 + shlen (mfa' - mfa)) in *.
  assert (SHE : SHF1 = shad (FA + mfa') /\ shad FA + shlen mfa = SHF0 /\ shad AB + shlen S <= shad (RB + au) /\ shad (RB + au) <= shad FA /\ shad FA <= SHF0 /\ SHF0 <= SHF1
                /\ SHF1 + shlen (536870912 - mfa') = shad (RB + 4294967296) /\ shad (RB + 4294967296) <= 17594333495296
                /\ shad RB = shad (al_space_beg L) + c * 536870912 /\ shad (RB + 4294967296) = shad (al_space_beg L) + (c + 1) * 536870912
                /\ shad (al_space_beg L) + 32 * 536870912 <= 17594333495296 /\ 2201439137792 <= shad RB /\ shad RB <= shad AB
                /\ shad (RB + au) + shlen (mu - au) = shad (RB + mu) /\ shad (RB + mu) <= shad FA
                /\ shad (RB + mu) + shlen (3758096384 - mu) = shad FA).
  { subst SHF1 SHF0. clearbody S mu au nf mfa nd RB FA RI CA AB half cnt nf' cnt' c k.
    generalize R8 AL16 SZM M8 A7 NEWMOD AU8 G1 G2 A1 A2 A5 A6 NEWB NEWM HC SP1 SP2 SP3 RBE FAE SZ16. clear. intros.
    rewrite !shad_div, !shlen_div in *. unfold ASHOFF in *. Z.div_mod_to_equations. lia. }
  destruct SHE as (SHE1 & SHE4 & SH1 & SH2 & SH3 & SH4 & SH5 & SH6 & SH9 & SH10 & SH11 & SH12 & SH13 & SH14 & SH15 & SH16).
  assert (KF : reckf0 (bv_unsigned sp) lo (al_t L) (al_ctx L) (al_space_beg L) c RB FA RI CA mu au nf mfa mfa' SHF0 SHF1).
  { unfold reckf0. pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR.
    pose proof (shlen_nonneg (536870912 - mfa') ltac:(clear -NEWB; lia)). pose proof (shlen_nonneg S ltac:(clear -SZ16; lia)).
    clear -H H0 CEIL LO SPR TL1 TL1u TL4u TL2 CL1 CL1u CL3 CL2 CL5 HC CAE SP1 SP2 RBE FAE RIE TSP SCX A1 A2 A5 A6 NEWB NEWM G1 G2 SH12 SH13 SH1 SH2 SH3 SH4 SH5 SH6 SH10 SH11.
    unfold c, K_BATCH_CLASS in *. unfold iclr, AIMG_LO, AIMG_HI in *; repeat match goal with H : _ /\ _ |- _ => destruct H end; repeat split; first [assumption | lia].   (* [comment removed for export] *) }
  assert (MUALL : munch (Wk0 (bv_unsigned sp) (al_t L) CA FA nf mfa' SHF0 SHF1 RI ++ ic_W L 1 31) m m').
  { eapply munch_weaken; [| exact MU2].
    unfold sub_fp, cd_W. cbv zeta. fold nf mfa CA FA RI. intros x Hx. apply outside_app in Hx. destruct Hx as [H13 HW].
    apply outside_app. split; [cbn [outside] in H13 |- *; clear -H13; lia|]. apply outside_app. split; [exact HW|].
    subst SHF0 SHF1. cbn [outside] in H13 |- *. clear -H13. lia. }
  pose proof WM2 as WMALL.
  assert (ICW_far : forall A k, (A + k <= al_t L \/ al_t L + 4096 <= A) -> disjoint_from (ic_W L 1 31) A k).
  { intros A k0 HA. apply ic_W_disjoint_gen; [unfold acache_addr; clear -HA; lia | clear; cbn; lia | clear; lia]. }
  assert (ICW_t : forall A k, (A + k <= al_t L + 292 \/ al_t L + 2768 <= A) -> disjoint_from (ic_W L 1 31) A k).
  { intros A k0 HA. apply ic_W_disjoint_gen; [unfold acache_addr; clear -HA; lia | clear; cbn; lia | clear; lia]. }
  (* [comment removed for export] *)
  assert (CPT : (AB - RB) / 16 = acompact c k).
  { subst AB RB. unfold aslot_addr, acompact. fold S. pose proof (proj2 (Z.div_exact S 16 ltac:(clear; lia)) SZM) as ES.
    set (q := S / 16) in ES. replace (aregion L c + k * S - aregion L c) with (k * q * 16) by (rewrite ES; clear; nia). rewrite Z.div_mul by (clear; lia). reflexivity. }
  unfold abatch_addr in CH'. fold c AB in CH'. rewrite CPT in CH'.
  (* [comment removed for export] *)
  assert (RCUT : drained = true -> rcut st c = Z.to_nat (cnt - half) /\ (Z.to_nat (cnt - half) < length (xc_cache (x_cls X c)))%nat /\ Z.to_nat (cnt' - 1) = Z.to_nat (cnt - half)).
  { intros D. unfold rcut, rcnt, rhalf. fold cnt half. subst cnt'. rewrite D in DRC |- *. split; [reflexivity|]. clear -LENCc DRC HALF MC2. split; lia. }
  (* [comment removed for export] *)
  assert (ACc : acache_cells L st_r X' m' c).
  { unfold acache_cells. cbv zeta. fold CA. rewrite GR. cbn [c_count]. unfold max_count. rewrite CIR. subst X'. rewrite (xrec_cls_self st X c k l1 l2 drained). cbn [xc_cache].
    unfold rcache'. pose proof RCUT as RC. destruct drained.
    - destruct (RC eq_refl) as (RC1 & RC2 & RC3). rewrite RC1. rewrite RC3 in CH'.
      exists (skipn (Datatypes.S (Z.to_nat (cnt - half))) (map (fun k0 => Z_to_bv 64 (acompact c k0)) (xc_cache (x_cls X c))) ++ tail).
      split; [exact RECc'|]. split.
      + rewrite upd_app_left in CH' by (rewrite length_map; exact RC2). rewrite upd_firstn_skipn in CH' by (rewrite length_map; exact RC2).
        rewrite map_app, <- List.firstn_map. cbn [map]. rewrite <- !app_assoc in CH' |- *. cbn [app] in CH' |- *. exact CH'.
      + rewrite !length_app, length_skipn, length_map, length_firstn. cbn [length]. clear -RC2 LCH. lia.
    - assert (TL : exists t0 tail', tail = t0 :: tail').
      { destruct tail as [|t0 tail']; [exfalso| exists t0, tail'; reflexivity]. cbn [length] in LCH. clear -LCH LENCc DRC MCR. lia. }
      destruct TL as (tw & tail' & ->). exists tail'.
      split; [exact RECc'|]. split.
      + subst cnt'. replace (Z.to_nat (cnt + 1 - 1)) with (length (map (fun k0 => Z_to_bv 64 (acompact c k0)) (xc_cache (x_cls X c)))) in CH' by (rewrite length_map; clear -LENCc; lia).
        rewrite upd_app_right, Nat.sub_diag in CH' by (clear; lia). cbn [upd] in CH'. rewrite map_app. cbn [map]. rewrite <- app_assoc. cbn [app]. exact CH'.
      + rewrite length_app. cbn [length] in LCH |- *. clear -LCH. lia. }
  (* [comment removed for export] *)
  assert (RCc : aregion_cells L st_r m' c).
  { unfold aregion_cells. cbv zeta. fold RI. rewrite GR. cbn [c_num_freed c_mapped_free_array c_allocated_user c_mapped_user].
    pose proof MTX16 as M2. rw_split M2 1%nat M2a M2b. clear M2a.
    eapply cells_frame in M2b; [| exact MUALL | exact WMALL | cbn [cells_size csize Nat.add];
      apply dj_app; [eapply (RK0_ri _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?RIE; clear -HC SP1; lia | apply ICW_far; rewrite RIE; clear -HC SP1 TSP; lia]].
    split. { rw_join MTX' M2b M16. exact M16. }
    split; [exact REG'|].
    split. { eapply junk_frame; [exact RJ4 | exact MUALL | exact WMALL |]. intros _.
             apply dj_app; [eapply (RK0_ri _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?RIE; clear -HC SP1; lia | apply ICW_far; rewrite RIE; clear -HC SP1 TSP; lia]. }
    split; [| exact J72'].
    eapply cells_frame; [exact EXH | exact MUALL | exact WMALL |]. cbn [cells_size csize Nat.add].
    apply dj_app; [eapply (RK0_ri _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?RIE; clear -HC SP1; lia | apply ICW_far; rewrite RIE; clear -HC SP1 TSP; lia]. }
  assert (FAB : 2201439137792 <= shad FA /\ SHF1 <= 17594333495296 /\ 0 <= shlen mfa /\ 0 <= shlen S
                /\ 0 <= shlen (mu - au) /\ 0 <= shlen (3758096384 - mu)).
  { pose proof (shlen_nonneg mfa ltac:(clear -A5 A6; lia)). pose proof (shlen_nonneg S ltac:(clear -SZ16; lia)). pose proof (shlen_nonneg (536870912 - mfa') ltac:(clear -NEWB; lia)).
    pose proof (shlen_nonneg (mu - au) ltac:(clear -A1; lia)). pose proof (shlen_nonneg (3758096384 - mu) ltac:(clear -A2; lia)).
    clear -H H0 H1 H2 H3 SH12 SH13 SH1 SH2 SH3 SH4 SH5 SH6. lia. }
  destruct FAB as (FB1 & FB2 & FB4 & FB5 & FB6 & FB7).
  assert (SB2 : SHF1 <= shad (RB + 4294967296)) by (clear -SH5 FB2 NEWB; pose proof (shlen_nonneg (536870912 - mfa') ltac:(lia)); lia).
  (* [comment removed for export] *)
  assert (FAc : afreearray L st_r X' m' c).
  { unfold afreearray. cbv zeta. fold FA. rewrite GR. cbn [c_num_freed c_mapped_free_array]. subst X'. rewrite (xrec_cls_self st X c k l1 l2 drained). cbn [xc_free].
    assert (FL' : u32arr bsegs m' FA (map (fun k0 : Z => Z_to_bv 64 (acompact c k0)) (xc_free (x_cls X c)))).
    { eapply u32arr_frame; [exact FL | exact MUALL | exact WMALL |]. rewrite length_map, LENF. fold nf.
      apply dj_app; [eapply (RK0_gap _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?FAE, ?RBE; clear -A1 A2 A5; lia | apply ICW_far; rewrite FAE; clear -A5 A6 HC TSP; lia]. }
    split; [| split; [exact FJ'|]].
    - unfold rfree'. pose proof RCUT as RC. destruct drained; [| exact FL'].
      destruct (RC eq_refl) as (RC1 & RC2 & RC3). rewrite RC1, map_app. apply u32arr_app; [exact FL'|].
      rewrite length_map, LENF. fold nf. specialize (DRA eq_refl).
      rewrite skipn_app, List.skipn_map, length_map in DRA. replace (Z.to_nat (cnt - half) - length (xc_cache (x_cls X c)))%nat with 0%nat in DRA by (clear -RC2; lia).
      rewrite skipn_O, firstn_app, length_map, length_skipn in DRA.
      replace (Z.to_nat half - (length (xc_cache (x_cls X c)) - Z.to_nat (cnt - half)))%nat with 0%nat in DRA by (clear -RC2 LENCc HALF MC2 DRC; lia).
      rewrite firstn_O, app_nil_r, firstn_all2 in DRA by (rewrite length_map, length_skipn; clear -RC2 LENCc HALF MC2 DRC; lia). exact DRA.
    - assert (FS1 : junk_at m' (shad FA) (shlen mfa)).
      { eapply junk_frame; [exact FSJ | exact MUALL | exact WMALL |]. intros _.
        apply dj_app; [eapply (RK0_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -FB1 FB2 FB4 SHE4 SH3 SH4; lia
                      | apply ICW_far; clear -FB1 FB2 SHE4 SH3 SH4 TL1u; lia]. }   (* [comment removed for export] *)
      destruct MFD as [Emfa|(_ & _ & Emfa & FI & _)].
      + rewrite Emfa. exact FS1.
      + replace (shlen mfa') with (shlen mfa + shlen (mfa' - mfa)) by (rewrite !shlen_div; clear -A7 NEWMOD NEWM A5 A6; Z.div_mod_to_equations; lia).
        apply junk_merge; [exact FS1 | rewrite SHE4; eapply fill_is_junk; exact FI | rewrite shlen_div; clear -A5 A6; Z.div_mod_to_equations; lia | rewrite shlen_div; clear -NEWM; Z.div_mod_to_equations; lia]. }
  (* [comment removed for export] *)
  assert (SLc : aslots L st_r X' m' c).
  { eapply (aslots_update L _ m m' MUALL WMALL st st_r X X' c k); [exact SLOTS0 | exact NDR | rewrite GR; reflexivity | rewrite GR; reflexivity | | |].
    - intros k' Hk' NE'. subst X'. rewrite (busy_of_xrec_other L st X BBatch c k nb b1 ctx l1 l2 drained XB WF) by (right; congruence). split; [reflexivity|]. split.
      + destruct (slot_in_region L st c k' ltac:(clear -SZ16; fold S; lia) ltac:(clear -A1; fold au; lia) Hk') as (Q1 & Q2 & Q3). fold RB S au in Q1, Q2, Q3.
        apply dj_app; [eapply (RK0_space_c _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -Q1 Q2 A1 SZ16; lia | apply ICW_far; clear -Q1 Q2 A1 A2 RBE HC TSP; unfold c, K_BATCH_CLASS in *; lia].
      + intros b Hb. destruct (busy_of_Some_facts X c k' b Hb) as (BIn & BC & BK). split; [exact BC|]. split; [exact BK|]. exact (awf_fits L st X b WF BIn).
    - intros POS. apply dj_app; [eapply (RK0_space_c _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -POS A1 G2 SZ16; lia | apply ICW_far; clear -A1 A2 RBE HC TSP; unfold c, K_BATCH_CLASS in *; lia].
    - intros _. subst X'. rewrite (busy_of_xrec_self L st X BBatch c k nb b1 ctx l1 l2 drained XB WF). fold S AB.
      (* [comment removed for export] *)
      specialize (SL k KR). rewrite (busy_of_X_self_g L st X BBatch c k nb b1 ctx l1 l2 XB WF) in SL.
      unfold aslot_busy in SL. cbn [xb_st xb_class xb_slot bany xb_alloc] in SL. fold S AB in SL.
      eapply junk_frame; [exact SL | exact MUALL | exact WMALL |]. intros POS.
      apply dj_app; [eapply (RK0_space_c _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -POS G1 G2 A1; lia | apply ICW_far; clear -G1 G2 A1 A2 RBE HC TSP; unfold c, K_BATCH_CLASS in *; lia]. }
  (* [comment removed for export] *)
  assert (SSc : aslot_shadow L st_r X' m' c).
  { eapply (aslot_shadow_update L _ m m' MUALL WMALL st st_r X X' c k); [exact SSH0 | exact NDR | rewrite GR; reflexivity | rewrite GR; reflexivity | | | | exact FB5].
    - intros k' Hk' NE'. fold S. subst X'. rewrite (busy_of_xrec_other L st X BBatch c k nb b1 ctx l1 l2 drained XB WF) by (right; congruence). split; [reflexivity|].
      destruct (slot_in_region L st c k' ltac:(clear -SZ16; fold S; lia) ltac:(clear -A1; fold au; lia) Hk') as (Q1 & Q2 & Q3). fold RB S au in Q1, Q2, Q3.
      pose proof (slot_aligned L c k' SAL HC) as AL'. fold S in AL'.
      assert (B : 2201439137792 <= shad (aslot_addr L c k') /\ shad (aslot_addr L c k') + shlen S <= shad (RB + au)).
      { rewrite !shad_div, !shlen_div in *. unfold ASHOFF in *. clear -Q1 Q2 AL' SZM SH12 R8 AU8. Z.div_mod_to_equations. lia. }
      apply dj_app; [eapply (RK0_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -B FB2 FB5 SH2 SH3 SH4; lia | apply ICW_far; clear -B FB2 SH2 SH3 SH4 TL1 TL1u TL4u; lia].
    - intros POS. fold RB mu au in POS |- *. apply dj_app; [eapply (RK0_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -POS FB2 FB5 FB6 SH1 SH2 SH3 SH4 SH12 SH13 SH14 SH15; lia
                                | apply ICW_far; clear -POS FB2 FB5 FB6 SH1 SH2 SH3 SH4 SH12 SH13 SH14 SH15 TL1u; lia].
    - intros _. subst X'. rewrite (busy_of_xrec_self L st X BBatch c k nb b1 ctx l1 l2 drained XB WF). cbn [slot_shadow_bytes]. fold S AB.
      specialize (SSL k KR). rewrite (busy_of_X_self_g L st X BBatch c k nb b1 ctx l1 l2 XB WF) in SSL.
      cbn [slot_shadow_bytes xb_n xb_st bany] in SSL. fold S AB in SSL. rewrite <- !repeat_app in SSL.
      destruct (proj1 (proj1 SSL)) as [LWF _]. cbn [cell_wf] in LWF. rewrite repeat_length in LWF. rewrite LWF in SSL.
      eapply cells_frame; [exact SSL | exact MUALL | exact WMALL |]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by exact FB5.
      apply dj_app; [eapply (RK0_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -SH12 SH13 FB2 SH1 SH2 SH3 SH4 FB5; lia
                    | apply ICW_far; clear -SH12 SH13 FB5 SH1 SH2 SH3 SH4 FB2 TL1 TL1u TL4u; lia]. }
  (* [comment removed for export] *)
  assert (AVc : ashadow_avail L st_r m' c).
  { unfold ashadow_avail. cbv zeta. rewrite GR. cbn [c_mapped_user c_mapped_free_array]. fold RB FA. split; [| exact AZF'].
    eapply azero_frame; [exact AZU | exact MUALL | exact WMALL |]. unfold K_FREEARR_OFF. intros POS.
    apply dj_app; [eapply (RK0_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -POS FB2 FB5 FB6 FB7 SH1 SH2 SH3 SH4 SH12 SH13 SH14 SH15 SH16; lia
                  | apply ICW_far; clear -POS FB2 FB5 FB6 FB7 SH1 SH2 SH3 SH4 SH12 SH13 SH14 SH15 SH16 TL1 TL1u TL4u; lia]. }
  (* [comment removed for export] *)
  assert (CLS' : forall c', 1 <= c' < 32 -> c' <> c ->
            aregion_cells L st_r m' c' /\ afreearray L st_r X' m' c' /\ aslots L st_r X' m' c' /\ aslot_shadow L st_r X' m' c' /\ ashadow_avail L st_r m' c' /\ acache_cells L st_r X' m' c').
  { intros c' Hc' NE. destruct (CLS c' Hc') as (RC2 & FA2 & SL2 & SS2). pose proof (AVL c' Hc') as AV2. destruct (CACHES c' Hc') as [tl (RH & RCH & RLEN)].
    destruct (PERC c' Hc') as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & BLENF & BLENC & BCNTB & BND & BRANGE).
    pose proof (size_of_class_facts c' Hc') as [SZ' SZM'].
    pose proof (GO c' NE) as G'.
    pose proof (region_other_geo L c c' ALO HC Hc' NE) as REGD. fold RB in REGD.
    destruct REGD as (RD1 & RD2 & RD3 & RD4 & RD5 & RD6 & RD7 & RD8 & RD9 & RD10 & RD11).
    assert (DJR : forall A k, aregion L c' <= A -> A + k <= aregion L c' + 4294967296 -> 0 <= k ->
                   disjoint_from (Wk0 (bv_unsigned sp) (al_t L) CA FA nf mfa' SHF0 SHF1 RI ++ ic_W L 1 31) A k).
    { intros A k0 HA HB Hk. apply dj_app; [eapply (RK0_reg_other _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -HA HB Hk RD1 RD2 RD3; lia
                                         | apply ICW_far; clear -HA HB Hk RD1 RD3 TSP; lia]. }
    assert (DJS : forall A k, shad (aregion L c') <= A -> A + k <= shad (aregion L c') + shlen 4294967296 -> 0 <= k ->
                   disjoint_from (Wk0 (bv_unsigned sp) (al_t L) CA FA nf mfa' SHF0 SHF1 RI ++ ic_W L 1 31) A k).
    { intros A k0 HA HB Hk. apply dj_app; [| apply ICW_far; clear -HA HB Hk RD9 RD10 TL1u; lia].
      destruct RD8 as [LOW|HIGH].
      - eapply (RK0_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -HA HB Hk LOW RD9 RD10 SB2 SH3 SH4 SH2 SH1 SH13 FB5; lia.
      - eapply (RK0_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -HA HB Hk HIGH RD9 RD10 SB2 SH3 SH4 SH2 SH1 SH13 FB5; lia. }
    assert (DJI : disjoint_from (Wk0 (bv_unsigned sp) (al_t L) CA FA nf mfa' SHF0 SHF1 RI ++ ic_W L 1 31) (aregion_info L c') 128).
    { apply dj_app; [eapply (RK0_ri _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?RD5, ?RIE; clear -Hc' NE HC; lia | apply ICW_far; rewrite ?RD5; clear -Hc' SP1 TSP; lia]. }
    split; [| split; [| split; [| split; [| split]]]].
    - eapply (aregion_cells_frame L _ m m' MUALL WMALL st); [exact RC2 | rewrite G'; reflexivity | rewrite G'; reflexivity | rewrite G'; reflexivity | rewrite G'; reflexivity | exact DJI].
    - eapply (afreearray_frame L _ m m' MUALL WMALL st st_r X); [exact FA2 | rewrite G'; reflexivity | rewrite G'; reflexivity | subst X'; rewrite (xrec_cls_other st X c k l1 l2 drained c' NE); reflexivity
        | exact BLENF | exact B5 | | clear -B6; lia |].
      + apply DJR; rewrite ?RD4; clear -B5 B6 B2; lia.
      + apply DJS; rewrite ?RD11, ?shlen_div; try (clear -B2 B5 B6; Z.div_mod_to_equations; lia).
    - eapply (aslots_update L _ m m' MUALL WMALL st st_r X _ c' (-1)); [exact SL2 | unfold ndist; rewrite G'; reflexivity | rewrite G'; reflexivity | rewrite G'; reflexivity | | |].
      + intros k0 Hk _. subst X'. rewrite (busy_of_xrec_other L st X BBatch c k nb b1 ctx l1 l2 drained XB WF) by (left; exact (not_eq_sym NE)). split; [reflexivity|]. split.
        * destruct (slot_in_region L st c' k0 ltac:(clear -SZ'; lia) ltac:(clear -B1; lia) Hk) as (Q1 & Q2 & Q3).
          apply DJR; [exact Q1 | clear -Q2 B1 B2; lia | clear -SZ'; lia].
        * intros b Hb. destruct (busy_of_Some_facts X c' k0 b Hb) as (BIn & BC & BK). split; [exact BC|]. split; [exact BK|]. exact (awf_fits L st X b WF BIn).
      + intros POS. apply DJR; clear -B1 B2 POS; lia.
      + intros HK. exfalso. clear -HK. lia.
    - eapply (aslot_shadow_update L _ m m' MUALL WMALL st st_r X _ c' (-1)); [exact SS2 | unfold ndist; rewrite G'; reflexivity | rewrite G'; reflexivity | rewrite G'; reflexivity | | | | rewrite shlen_div; clear -SZ'; Z.div_mod_to_equations; lia].
      + intros k0 Hk _. subst X'. rewrite (busy_of_xrec_other L st X BBatch c k nb b1 ctx l1 l2 drained XB WF) by (left; exact (not_eq_sym NE)). split; [reflexivity|].
        destruct (slot_in_region L st c' k0 ltac:(clear -SZ'; lia) ltac:(clear -B1; lia) Hk) as (Q1 & Q2 & Q3).
        apply DJS.
        * apply shad_mono. exact Q1.
        * rewrite !shad_div, !shlen_div in *. clear -Q1 Q2 B1 B2 RD7. Z.div_mod_to_equations. lia.
        * rewrite shlen_div. clear -SZ'; Z.div_mod_to_equations; lia.
      + intros POS. apply DJS.
        * apply shad_mono. clear -B1; lia.
        * rewrite !shad_div, !shlen_div in *. clear -B1 B2 RD7. Z.div_mod_to_equations. lia.
        * clear -POS; lia.
      + intros HK. exfalso. clear -HK. lia.
    - eapply (ashadow_avail_frame L _ m m' MUALL WMALL st); [exact AV2 | rewrite G'; reflexivity | rewrite G'; reflexivity | |]; unfold K_FREEARR_OFF, K_FREEARR_MAX.
      + intros POS. apply DJS.
        * apply shad_mono. clear -B1; lia.
        * rewrite !shad_div, !shlen_div in *. clear -B1 B2 RD7. Z.div_mod_to_equations. lia.
        * clear -POS; lia.
      + intros POS. apply DJS.
        * apply shad_mono. rewrite RD4. clear -B5 B6; lia.
        * rewrite RD4. rewrite !shad_div, !shlen_div in *. clear -B5 B6 RD7. Z.div_mod_to_equations. lia.
        * clear -POS; lia.
    - unfold acache_cells. cbv zeta. rewrite G'. unfold max_count. rewrite CIR. subst X'. rewrite (xrec_cls_other st X c k l1 l2 drained c' NE). exists tl.
      split; [exact (RECS' c' ltac:(clear -Hc'; lia) NE)|]. split; [| exact RLEN].
      eapply u32arr_frame; [exact RCH | exact MUALL | exact WMALL |]. rewrite length_app, length_map.
      replace (Z.of_nat (length (xc_cache (x_cls X c')) + length tl)) with 16 by (clear -RLEN; lia).
      apply dj_app; [eapply (RK0_rec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?RD6, ?CAE; clear -Hc' NE HC; lia | change (4 * 16) with 64; apply ic_W_disjoint_chunks]. }
  (* [comment removed for export] *)
  assert (BB : forall b, In b (x_busy X') ->
      al_space_beg L <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= al_space_beg L + 137438953472
      /\ (xb_alloc L b + size_of_class (xb_class b) <= RB + mu \/ xb_alloc L b + size_of_class (xb_class b) <= RB \/ RB + 4294967296 <= xb_alloc L b)).
  { intros b Hb. subst X'. pose proof (xrec_sub st X BBatch c k nb b1 ctx l1 l2 drained XB b Hb) as HbX. apply In_xrec in Hb.
    destruct (BUSY b HbX) as [CLB _].
    destruct (PERC (xb_class b) CLB) as (Q1 & Q2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & QR).
    pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
    assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
    { apply QR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
      apply filter_In. split; [exact HbX| apply Z.eqb_refl]. }
    pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -QS; lia) (proj1 Q1) KB) as (P5 & P4 & P0).
    unfold xb_alloc.
    destruct (Z.eq_dec (xb_class b) c) as [EC|NC].
    - rewrite EC in P5, P4, Q1, Q2 |- *. fold RB au mu S in P5, P4, Q1, Q2.
      split; [clear -P5 RBE HC; unfold c, K_BATCH_CLASS in *; lia|]. split; [clear -P4 A1 A2 RBE HC; unfold c, K_BATCH_CLASS in *; lia|]. left. clear -P4 A1; lia.
    - pose proof (region_other_geo L c (xb_class b) ALO HC CLB NC) as (R1 & R2 & R3 & _). fold RB in R2.
      split; [clear -P5 R1; lia|]. split; [clear -P4 Q1 Q2 R3; lia|].
      right. destruct R2 as [D|D]; [left; clear -D P4 Q1 Q2; lia | right; clear -D P5; lia]. }
  (* [comment removed for export] *)
  assert (DJimg : forall A k, 65536 <= A -> 0 <= k -> A + k <= 6443008 ->      (* [comment removed for export] *)
            disjoint_from (Wk0 (bv_unsigned sp) (al_t L) CA FA nf mfa' SHF0 SHF1 RI ++ ic_W L 1 31) A k).
  { intros A k0 H1 H2 H3. apply dj_app; [eapply (RK0_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); assumption | apply ICW_far; clear -H1 H3 TL4u; lia]. }
  assert (DJt : forall A k, al_t L <= A -> 0 <= k ->
            (A + k <= al_t L + 288 \/ (al_t L + 2768 <= A /\ A + k <= al_t L + 2784) \/ (al_t L + 2792 <= A /\ A + k <= al_t L + 2800) \/ (al_t L + 3168 <= A /\ A + k <= al_t L + 4096)) ->
            disjoint_from (Wk0 (bv_unsigned sp) (al_t L) CA FA nf mfa' SHF0 SHF1 RI ++ ic_W L 1 31) A k).
  { intros A k0 H1 H2 H3. apply dj_app; [| apply ICW_t; clear -H3; lia].
    destruct H3 as [H3|[H3|[H3|H3]]];
      [ eapply (RK0_tlow _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF)
      | eapply (RK0_tstat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF)
      | eapply (RK0_tstat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF)
      | eapply (RK0_thigh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF)]; clear -H1 H2 H3; lia. }
  assert (DJctx : forall A k, al_ctx L <= A -> A + k <= al_ctx L + 4096 -> 0 <= k ->
            disjoint_from (Wk0 (bv_unsigned sp) (al_t L) CA FA nf mfa' SHF0 SHF1 RI ++ ic_W L 1 31) A k).
  { intros A k0 H1 H2 H3. apply dj_app; [| apply ICW_far; clear -H1 H2 H3 CL5; lia].
    eapply (RK0_obj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); atop_facts; clear -H1 H2 H3 CL1u CL3 CL2 CL5 SCX; unfold AIMG_HI in *; lia. }   (* [comment removed for export] *)
  (* [comment removed for export] *)
  assert (WF' : awf L st_r X').
  { subst X'. eapply (awf_xrec L st X BBatch c k nb b1 ctx l1 l2 drained XB WF ltac:(intros p; discriminate) DRC st_r mfa');
      [exact EF10 | exact EF9 | exact CIR | exact EF1 | exact EF2 | exact GO | | clear -NEWB; unfold K_FREEARR_MAX; subst nf'; unfold rnf', rhalf; fold nf half; destruct drained; lia | exact NEWMOD].
    rewrite GR. unfold rnf', rcnt', rcnt, rhalf. fold nf half cnt. subst nf' cnt'. destruct drained; f_equal; lia. }
  assert (RT' : arep_rt L m').
  { eapply arep_rt_frame; [exact MUALL | exact WMALL | exact RT |]. unfold rt_hulls, ATP88, ATSD.
    repeat (apply Forall_cons; [cbn [fst snd]; first [apply DJimg; clear; lia | apply DJctx; clear; lia] |]). apply Forall_nil. }
  assert (INST' : ainstance L st_r m').
  { eapply ainstance_frame; [exact MUALL | exact WMALL | exact INST | exact EF8 | exact EF7 | | |]; apply DJimg; clear; unfold AINSTANCE; lia. }
  assert (THR' : athread L st_r X' m').
  { unfold athread. split; [| split; [| split; [| split; [| split]]]].
    - eapply cells_frame; [exact T0c | exact MUALL | exact WMALL |]. cbn [cells_size csize Nat.add]. apply DJt; clear; lia.
    - eapply cells_frame; [exact T40 | exact MUALL | exact WMALL |]. cbn [cells_size csize Nat.add]. apply DJt; clear; lia.
    - intros c' Hc'. destruct (Z.eq_dec c' c) as [->|NE]; [exact ACc | exact (proj2 (proj2 (proj2 (proj2 (proj2 (CLS' c' Hc' NE))))))].
    - apply (junk_merge m' (al_t L + 2768) 16 16); [| | clear; lia | clear; lia].
      + destruct (junk_split m (al_t L + 2768) 16 16 CSTATS ltac:(clear; lia) ltac:(clear; lia)) as [J16 _].
        eapply junk_frame; [exact J16 | exact MUALL | exact WMALL | intros _; apply DJt; clear; lia].
      + apply (junk_merge m' (al_t L + 2768 + 16) 8 8); [| | clear; lia | clear; lia].
        * replace (al_t L + 2768 + 16) with (al_t L + 2784) by (clear; lia). pose proof (junk_of_cells m' _ _ STA') as J. cbn in J. exact J.
        * destruct (junk_split m (al_t L + 2768) 24 8 CSTATS ltac:(clear; lia) ltac:(clear; lia)) as [_ J8].
          replace (al_t L + 2768 + 16 + 8) with (al_t L + 2768 + 24) by (clear; lia).
          eapply junk_frame; [exact J8 | exact MUALL | exact WMALL | intros _; apply DJt; clear; lia].
    - exists sj'. split; [exact STATS' | exact LSJ'].
    - eapply cells_frame; [exact UNW | exact MUALL | exact WMALL |]. cbn [cells_size csize Nat.add]. apply DJt; clear; lia. }
  (* [comment removed for export] *)
  pose proof (ao_space L ALO) as RSP.
  set (WH := [(bv_unsigned sp - 688, bv_unsigned sp); (al_t L + 208, al_t L + 3168); (RI, RI + 128);
              (FA + 4 * nf, FA + 536870912); (SHF0, shad RB + 536870912)]).
  assert (MUH : munch WH m m').
  { eapply munch_weaken; [| exact MUALL]. unfold sub_fp. intros x Hx. subst WH. cbn [outside] in Hx. destruct Hx as (O1 & O2 & O3 & O4 & O5 & _).
    apply outside_app. split.
    - cbn [outside]. clear -O1 O2 O3 O4 O5 SH5 FB2 NEWB CAE HC SH10 SH9 SHE1 NEWM A5 A6.
      pose proof (shlen_nonneg (536870912 - mfa') ltac:(lia)). unfold c, K_BATCH_CLASS in *. repeat split; try exact I; lia.
    - apply ic_W_outside; [unfold acache_addr; clear -O2; lia | clear; cbn; lia | clear; lia]. }
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR.
  assert (HQ0 : AQdr (qr_unbatch R) 0 0 L st X' m) by (subst X'; eapply AQdr_unbatch; [exact HQ | exact EB | exact EP | exact XB | exact WF]).
  assert (QU : quar_untouched L X' WH).
  { unfold quar_untouched. subst WH. unfold AINSTANCE in *.
    repeat (apply Forall_cons; [cbn [fst snd];
      split; [clear -CEIL LO TL1 TL1u TL4u TL2 TSP SP1 SP2 RIE RBE FAE HC A1 A2 A5 G1 G2 G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 FB5 SB2 SH6 NEWB; unfold c, K_BATCH_CLASS in *; lia|];
      split; [clear -CEIL LO TL1 TL1u TL4u TL2 TSP SP1 SP2 RIE RBE FAE HC A1 A2 A5 G1 G2 G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 FB5 SB2 SH6 NEWB; unfold c, K_BATCH_CLASS in *; lia|];
      split; [clear -CEIL LO TL1 TL1u TL4u TL2 TSP SP1 SP2 RIE RBE FAE HC A1 A2 A5 G1 G2 G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 FB5 SB2 SH6 NEWB; unfold c, K_BATCH_CLASS in *; lia|];
      split; [clear -CEIL LO TL1 TL1u TL4u TL2 TSP SP1 SP2 RIE RBE FAE HC A1 A2 A5 G1 G2 G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 FB5 SB2 SH6 NEWB; unfold c, K_BATCH_CLASS in *; lia|];
      intros b Hb; destruct (BB b Hb) as (Bb1 & Bb2 & Bb3); destruct (xb_st b); [exact I| |];
      clear -Bb1 Bb2 Bb3 CEIL LO TL1 TL1u TL4u TL2 TSP SP1 SP2 RIE RBE FAE HC A1 A2 A5 G1 G2 G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 FB5 SB2 SH6 NEWB; unfold c, K_BATCH_CLASS in *; lia |]).
    apply Forall_nil. }
  assert (QSM : quar_same st st_r X' X').
  { unfold quar_same. rewrite EF3, EF4, EF5, EF6, EF10. repeat (split; [reflexivity|]).
    split; intros b Hb; destruct (xb_st b); first [exact I | exact Hb]. }
  assert (HQ' : AQdr (qr_unbatch R) 0 0 L st_r X' m').
  { eapply AQdr_frame; [exact HQ0 | exact MUH | exact WMALL | exact QU | exact QSM]. }
  assert (SU : sec_untouched L WH).
  { unfold sec_untouched, aknown. subst WH. unfold AINSTANCE, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *.
    apply Forall_cons; [cbn [fst snd]; intros a Ha; do 4 right; left; clear -Ha CEIL LO; lia |].
    apply Forall_cons; [cbn [fst snd]; intros a Ha; do 5 right; left; clear -Ha TL1 TL1u TL4u TL2; lia |].
    apply Forall_cons; [cbn [fst snd]; intros a Ha; do 7 right; left; clear -Ha RSP RIE HC; unfold c, K_BATCH_CLASS in *; lia |].
    apply Forall_cons; [cbn [fst snd]; intros a Ha; do 7 right; left; clear -Ha RSP RBE FAE HC A5; unfold c, K_BATCH_CLASS in *; lia |].
    apply Forall_cons; [cbn [fst snd]; intros a Ha; right; left; clear -Ha HC SH9 SH10 SH11 SH13 SH1 SH2 SH3 FB5; unfold c, K_BATCH_CLASS in *; lia |].
    apply Forall_nil. }
  assert (SSM : sec_same st st_r).
  { unfold sec_same. rewrite EF7, EF8, EF9, EF1. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [intros; first [apply iff_refl | clear; tauto | tauto]|].   (* [comment removed for export] *)
    rewrite (sec_chunks_of_eq st st_r EF1 EF3 EF5). apply Permutation_refl. }
  assert (HS' : ASECc cs L st_r X' m').
  { eapply (hs_frame _ (HL (qr_unbatch R) cs) L st st_r X X' m m'); [exact HS | exact MUH | exact WMALL | exact SU | exact SSM]. }
  assert (HD' : AD L m').
  { eapply (hd_frame _ (HL R cs) L m m'); [exact HD | exact MUH | exact WMALL |]. subst WH.
    pose proof (ao_nodes L ALO) as (_ & ON1 & ON3 & ONs & _). pose proof (ao_store L ALO) as (_ & OS1 & OS3 & OSs & _). unfold sclr, KLS in ONs, OSs.
    pose proof (ad_nodes_res L ALO) as DNR. pose proof (ad_store_res L ALO) as DSR. pose proof (ad_t_nodes L ALO) as DTN. pose proof (ad_t_store L ALO) as DTS.
    unfold adisj, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *.
    (* [comment removed for export] *)
    repeat (apply Forall_cons; [cbn [fst snd]; intros a Ha; split; [| split];
      [ clear -Ha CEIL LO TL4u TL2 SP1 SP2 RSP RIE RBE FAE HC A5 A6 NEWB G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 SB2 SH6 FB5; unfold c, K_BATCH_CLASS in *; lia
      | clear -Ha CEIL LO TL2 SP1 SP2 RSP RIE RBE FAE HC A5 A6 NEWB G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 SB2 SH6 FB5 ON1 ON3 ONs DNR DTN; unfold c, K_BATCH_CLASS in *; lia
      | clear -Ha CEIL LO TL2 SP1 SP2 RSP RIE RBE FAE HC A5 A6 NEWB G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 SB2 SH6 FB5 OS1 OS3 OSs DSR DTS; unfold c, K_BATCH_CLASS in *; lia ] |]). apply Forall_nil. }
  assert (AR' : AREP (AHr (qr_unbatch R) cs) L st_r X' m').
  { split; [exact WF'|]. split; [exact RT'|]. split; [exact INST'|]. split; [exact THR'|]. split.
    { intros c' Hc'. destruct (Z.eq_dec c' c) as [->|NE].
      - split; [exact RCc|]. split; [exact FAc|]. split; [exact SLc| exact SSc].
      - destruct (CLS' c' Hc' NE) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6). split; [exact Y1|]. split; [exact Y2|]. split; [exact Y3| exact Y4]. }
    split; [exact HQ'|]. split; [exact HS'|]. split; [exact HD'|].
    split; [eapply arelro_frame; [exact MUALL | exact HRO | apply DJimg; clear; unfold ARELRO_LO, ARELRO_HI; lia]|].
    split; [eapply arep_rt2_frame; [exact MUALL | exact WMALL | exact RT2 | | |]; apply DJimg; clear; lia|].
    split; [| eapply arep_rt3_frame; [exact MUALL | exact WMALL | exact RT3 |]; unfold rt3_hulls;
              repeat (apply Forall_cons; [cbn [fst snd]; apply DJimg; clear; lia |]); apply Forall_nil].
    intros c' Hc'. destruct (Z.eq_dec c' c) as [->|NE]; [exact AVc | exact (proj1 (proj2 (proj2 (proj2 (proj2 (CLS' c' Hc' NE))))))]. }
  (* [comment removed for export] *)
  assert (ARNG' : arng L RNG' st_r).
  { pose proof (arng_mono L RNG RNG' st FPLE ARNG) as AM.
    destruct AM as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & RC & RPA & RSC & RPSH).
    unfold arng. split; [exact Z1|]. split; [exact Z2|]. split; [exact Z3|]. split; [exact Z4|]. split; [exact Z5|].
    split; [exact Z6|]. split; [exact Z7|]. split; [exact Z8|]. split; [exact Z9|].
    split; [| split; [rewrite EF8; exact RPA| split; [rewrite (sec_chunks_of_eq st st_r EF1 EF3 EF5); exact RSC| exact RPSH]]].
    intros c' Hc'. cbv zeta. destruct (Z.eq_dec c' c) as [->|NE].
    - rewrite GR. cbn [c_mapped_user c_mapped_free_array]. fold RB FA.
      destruct (RC c HC) as (Q1 & Q2 & Q3 & Q4). fold RB FA mu mfa in Q1, Q2, Q3, Q4.
      split; [exact Q1|]. split; [exact Q2|]. split.
      + destruct MFD as [Emfa|(_ & _ & Emfa & _ & RF & RSF & BW)]; [rewrite Emfa; exact Q3|].
        replace mfa' with (mfa + (mfa' - mfa)) by (clear; lia). apply rng_merge; [exact BW | clear -A5 A6; lia | clear -NEWM; lia | exact Q3 | exact RF].
      + destruct MFD as [Emfa|(_ & _ & Emfa & _ & RF & RSF & BW)]; [rewrite Emfa; exact Q4|].
        assert (M8c : mfa mod 8 = 0 /\ mfa' mod 8 = 0) by (clear -A7 NEWMOD; Z.div_mod_to_equations; lia). destruct M8c as [M8c M8d].
        replace (shlen mfa') with (shlen mfa + shlen (mfa' - mfa)) by (rewrite !shlen_div; clear -M8c M8d; Z.div_mod_to_equations; lia).
        apply rng_merge; [exact BW | rewrite shlen_div; clear -A5 A6; Z.div_mod_to_equations; lia | rewrite shlen_div; clear -NEWM; Z.div_mod_to_equations; lia | exact Q4 |].
        rewrite SHE4. exact RSF.
    - rewrite (GO c' NE). exact (RC c' Hc'). }
  (* [comment removed for export] *)
  exists X', mfa'.
  split; [exact MU2|]. split; [exact WMALL|]. split; [clear -NEWB NEWM; lia|]. split; [exact AR'|]. split; [exact ARNG'|]. split; [exact CIR|].
  split; [exact EF1|]. split; [exact EF2|]. split; [exact EF3|]. split; [exact EF4|]. split; [exact EF5|]. split; [exact EF6|].
  split; [exact EF7|]. split; [exact EF8|]. split; [exact EF9|]. split; [exact EF10|]. split; [exact GO|].
  split; [intros b Hb; subst X'; exact (xrec_sub st X BBatch c k nb b1 ctx l1 l2 drained XB b Hb)|].
  intros b p Hb Sb. subst X'. exact (xrec_live st X BBatch c k nb b1 ctx l1 l2 drained XB ltac:(intros p'; discriminate) b p Hb Sb).
Qed.

(* [comment removed for export] *)
Lemma pendb_busy : forall L st X R m kb,
  AQdr R 0 0 L st X m -> qr_pendb R = [kb] ->
  exists nb b1 ctx l1 l2, x_busy X = l1 ++ bany BBatch K_BATCH_CLASS kb nb b1 ctx :: l2.
Proof.
  intros L st X R m kb (_ & _ & _ & _ & _ & _ & CP & _) EB.
  destruct (qcoupled_rec_bslot_busy L st X R kb CP ltac:(unfold qr_bslots; rewrite EB; apply in_app_iff; right; left; reflexivity)) as (b & Hb & Sb & Cb & Kb).
  destruct (in_split _ _ Hb) as (l1 & l2 & E). destruct b as [bc bk bn bs bb1 bctx]. cbn in Sb, Cb, Kb. subst bs bc bk.
  exists bn, bb1, bctx, l1, l2. exact E.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem acdealloc24 :
  forall {RT} (k : astate -> AM RT) (Q : RT -> footprint -> machine_state -> Prop)
         (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (X : aconc) (R : qrconc) (cs : list achunk)
         (kb lo : Z),
  alayout_ok L -> arng L RNG st -> AREP (AHr R cs) L st X m ->
  qr_pendb R = [kb] -> qr_pend R = [] ->
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 688 ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 (al_t L + 208) -> a1 = Z_to_bv 64 AINSTANCE -> a2 = Z_to_bv 64 K_BATCH_CLASS -> a3 = Z_to_bv 64 (abatch_addr L kb) ->
  rng RNG lo (bv_unsigned sp - lo) ->
  (forall stX X' RNG' ms', acd24_ret L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st X R cs lo m stX X' RNG' ms' ->
     implS bsegs RNG' (aembed ATOP (k stX)) (epostF Q) ms') ->
  implS bsegs RNG (aembed ATOP (cache_dealloc st K_BATCH_CLASS k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 cdealloc_entry) fc None m (seg_rom bsegs)).
Proof.
  intros RT k Q L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st X R cs
         kb lo ALO ARNG AR EB EP MI ST CEIL LO TP Ha0 Ha1 Ha2 Ha3 RSTK KONT.
  set (c := K_BATCH_CLASS) in *.
  pose proof AR as AR0. destruct AR0 as (WF & RT0 & INST & THR & CLS & HQ & HS & HD & HRO & RT2 & AVL & RT3).
  cbn [ah_quar ah_sec ah_depot AHr ARecyc1P.AHr] in HQ, HS, HD.
  destruct (pendb_busy L st X R m kb HQ EB) as (nb & b1 & ctx & l1 & l2 & XB). fold c in XB.
  destruct (any_range L st X BBatch c kb nb b1 ctx l1 l2 XB WF) as [HC KR].
  destruct THR as (T0c & T40 & CACHES & CSTATS & [sj [STATS LSJ]] & UNW).
  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  destruct (PERC c HC) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & LENF & LENC & CNTB & ND & RANGE).
  destruct (CLS c HC) as (RCELLS & FARR & SLOTS & SSH). destruct (AVL c HC) as [AZU AZF].
  destruct RCELLS as (MTX16 & REG & RJ4 & EXH & RJ56). destruct FARR as (FL & FJ & FSJ).
  pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & SP4).
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4).
  pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5).
  pose proof TL1 as TL1u. pose proof TL4 as TL4u. pose proof CL1 as CL1u. unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in TL1u, TL4u, CL1u.   (* [comment removed for export] *)
  pose proof (alayout_res_disj L ALO) as [SCX TSP].
  pose proof ARNG as ARNG0. destruct ARNG0 as (RIMG & RT4 & RCTX & RNO & RSTO & RRI & RFK & RSFK & RDTLS & RCLS & RPA & RSECS & RPSH).
  destruct (RCLS c HC) as (RREG & RSREG & RFA & RSFA).
  pose proof RT0 as RT1.
  destruct RT1 as (GPG & GOT & GOT80 & RIC & LS1 & REAL & IMAX4 & FLG5 & FLG & HPP & SHB & CANP & TI & TK & INI2 & LAY & MCS & OOM3
                    & PGC & HK2 & CF8 & CF34 & CSMT & T88 & TSD & LS2 & CT8 & CT).
  destruct RT2 as (DPM & MLIM & RWCS).
  destruct INST as (I32 & I48 & I64 & I72 & I112 & I680 & I984 & I40 & I56).
  assert (MC : m3_cells L m).
  { unfold m3_cells, poison_cells, rmap_cells, AINSTANCE in *. repeat lazymatch goal with |- _ /\ _ => split end; assumption. }
  pose proof MTX16 as MTX. rw_split MTX 1%nat MTX MTXb. clear MTXb.
  destruct (junk_split m (al_t L + 2768) 16 16 CSTATS ltac:(lia) ltac:(lia)) as [_ CSb].
  destruct (junk_split m (al_t L + 2768 + 16) 8 8 CSb ltac:(lia) ltac:(lia)) as [CS8 _].
  replace (al_t L + 2768 + 16) with (al_t L + 2784) in CS8 by lia. destruct (c8_of_junk m _ CS8) as [sta STA].
  destruct (CACHES c HC) as [tail (RECc & CH & LCH)]. cbv zeta in CH. cbv zeta in LCH.
  pose proof (cache_vals_lt L st X c tail WF HC LCH) as CH31.
  destruct (nf_bound L st X c WF HC) as [NFA NFN].
  pose proof (slot_geo L st X c kb ALO WF HC KR) as (S1 & S2 & AL16 & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & R8 & M8).
  (* [comment removed for export] *)
  eapply (cdealloc_spec RNG k Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L st c (abatch_addr L kb) lo
            sj (map (fun k0 => Z_to_bv 64 (acompact c k0)) (xc_cache (x_cls X c)) ++ tail) sta);
  try lazymatch goal with
       | |- forall stX RNG' m' t0', _ => idtac
       | |- stk _ _ _ _ => exact ST
       | |- ATOP <= _ => exact CEIL
       | |- _ <= bv_unsigned _ - _ => exact LO
       | |- mem_inv _ _ => exact MI
       | |- m3_cells _ _ => exact MC
       | |- rw_cells _ _ (aregion_info _ _) _ => exact MTX
       | |- rw_cells _ _ (aregion_info _ _ + 16) _ => exact REG
       | |- junk_at _ (aregion_info _ _ + 72) _ => exact RJ56
       | |- junk_at _ (afreearr _ _ + _) _ => exact FJ
       | |- rw_cells _ _ (al_t _ + 2784) _ => exact STA
       | |- u64arr _ _ _ _ => exact STATS
       | |- u32arr _ _ _ _ => exact CH
       | |- Forall _ _ => exact CH31
       | |- length (map _ _ ++ _) = _ => rewrite length_app, length_map; exact LCH
       | |- length _ = _ => exact LSJ
       | |- azero _ (shad (afreearr _ _ + _)) _ => exact AZF
       | |- a_space_beg _ = _ => exact SBE
       | |- rng_aimg _ => exact RIMG
       | |- rng _ _ (bv_unsigned _ - _) => exact RSTK
       | |- rng _ (aregion_info _ _) _ => eapply rng_sub'; [exact RRI|]; unfold aregion_info, ARI_STRIDE, K_SPACE_EXTRA; clear -HC; unfold K_NUM_CLASSES in HC; lia
       | |- rng _ (afreearr _ _) _ => exact RFA
       | |- rng _ (al_ctx _) _ => eapply rng_sub'; [exact RCTX|]; clear; lia
       | |- rng _ (al_t _) _ => exact RT4
       | |- @eq word _ _ => first [exact TP | exact Ha0 | exact Ha1 | exact Ha2 | exact Ha3]
       | |- _ \/ _ => first [exact CL5 | exact TSP | clear -SCX; unfold K_SPACE_SIZE, K_SPACE_EXTRA in *; lia]
       | |- forall j, _ -> arec_hdr _ _ _ _ _ _ => intros j Hj; destruct (CACHES j ltac:(unfold K_NUM_CLASSES; clear -Hj; lia)) as [tl (RH & _ & _)]; exact RH
       | |- forall j, _ -> 0 <= _ <= _ => intros j Hj; destruct (PERC j ltac:(unfold K_NUM_CLASSES; clear -Hj; lia)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CB2 & _); exact CB2
       end.
  all: lazymatch goal with
       | |- forall stX RNG' m' t0', _ => idtac
       | |- aregion _ _ <= abatch_addr _ _ => exact G1
       | |- abatch_addr _ _ < aregion _ _ + _ => unfold ndist in KR; unfold K_REGION, K_FREEARR_OFF in *; change (2^32) with 4294967296; unfold abatch_addr; fold c; clear -G1 G2 G3 G4 S1; lia
       | |- al_ctx _ + 4096 <= _ => clear -CL2; atop_facts; lia
       | |- ?g => first [assumption | idtac "REMAINS" g]
       end.
  (* [comment removed for export] *)
  intros stX RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' CDR.
  destruct (cd24_store L RNG RNG' sp m m' st stX X R cs kb nb b1 ctx lo l1 l2 tail ALO ARNG AR EB EP XB CEIL LO CH LCH CDR)
    as (X' & mfa' & MU & WM & MFB & AR' & ARNG' & CIN & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & GC & XS & XL).
  destruct CDR as (FPLE & dr & mfa2 & sj2 & sta2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & MIT & STT & _).
  eapply KONT. unfold acd24_ret. split; [exact FPLE|]. do 16 eexists. exists mfa'. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MIT|]. split; [exact STT|]. split; [exact MFB|]. split; [exact AR'|]. split; [exact ARNG'|].
  split; [exact CIN|]. split; [exact L1|]. split; [exact L2|]. split; [exact L3|]. split; [exact L4|]. split; [exact L5|]. split; [exact L6|].
  split; [exact L7|]. split; [exact L8|]. split; [exact L9|]. split; [exact L10|]. split; [exact GC|].
  split; [exact XS| exact XL].
Qed.
End P.
End CANSEC1.
