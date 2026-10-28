(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FMapPositive.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import AsanAllocModel.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AllocWf AllocKit AllocRep AllocRepFacts AllocRepFacts2 AllocRepX
     AsDepotInv AsDepotHash AsUnwind CidBits AW_AllocBase AW_MallocBase AW_IAInit AW_Put1 AW_Enqueue1 AW_Put2 AS_Free1 AS_Free2 AllocWalkKit
     AG_MallocModel AG_WFHit AG_Malloc AG_Malloc2 AG_FreeModel AG_WFFree AG_Free1 AG_FreeFacts AG_Free2 AG_RepQ.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import PerfLia.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac lia ::=
  dle_wrap ltac:(first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ]).

Section HCW.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
Lemma map_qb_addr_snoc : forall r (b b' : qbatch), qb_addr b' = qb_addr b -> map qb_addr (r ++ [b']) = map qb_addr (r ++ [b]).
Proof. intros r b b' E. rewrite !map_app. cbn [map]. rewrite E. reflexivity. Qed.
Lemma wlist_app : forall l1 l2, wlist (l1 ++ l2) = wlist l1 ++ wlist l2.
Proof. intros l1 l2. unfold wlist. apply map_app. Qed.

Lemma need_new_false : forall t, qc_list t <> [] -> qb_count (last (qc_list t) (mkQB 0 0 0 [])) < kBatchCount -> need_new t = false.
Proof. intros t. unfold need_new. destruct (qc_list t) as [|b r]; intros NE LT; [exfalso; exact (NE eq_refl)| apply Z.leb_gt; exact LT]. Qed.

(* [comment removed for export] *)
Lemma batch_addrs_nodup : forall s, ast_ok s -> List.NoDup (map qb_addr (qc_list (as_tq (a_st s)) ++ qc_list (as_gq (a_st s)))).
Proof.
  intros s OK. destruct OK as [_ W]. destruct W as (_ & ND & _). rewrite (carved_addr_list_eq s) in ND.
  apply NoDup_app_r in ND. apply NoDup_app_r in ND. exact ND.
Qed.


(* [comment removed for export] *)
Lemma NoDup_map_transfer {A B C} : forall (f : A -> B) (g : A -> C) (l : list A),
  List.NoDup (map f l) -> (forall x y, In x l -> In y l -> g x = g y -> f x = f y) -> List.NoDup (map g l).
Proof.
  intros f g l. induction l as [|x l IH]; intros ND INJ; cbn; [constructor|]. cbn in ND. apply NoDup_cons_iff in ND. destruct ND as [NI ND].
  constructor.
  - intros Hin. apply in_map_iff in Hin. destruct Hin as (y & E & Hy). apply NI. apply in_map_iff. exists y. split; [| exact Hy].
    symmetry. apply INJ; [left; reflexivity| right; exact Hy| symmetry; exact E].
  - apply IH; [exact ND|]. intros a b Ha Hb. apply INJ; right; assumption.
Qed.
End HCW.

(* [comment removed for export] *)
Section Bounds.
  Context {HCEIL : HeapCeil}.
  Variables (s : ast) (m : mem).
  Hypothesis R : AREP s m.
  Let st := a_st s.
  Let OK : ast_ok s. Proof. exact (proj1 R). Qed.
  Let WFs : WF st. Proof. exact (proj2 OK). Qed.

  (* [comment removed for export] *)
  Lemma used_lt47 : forall ch, In ch (chunk_list st) -> 1 <= ch_used ch < 2^47.
  Proof.
    intros ch Hin. pose proof (chunk_geom s OK ch Hin) as (G1 & G2 & G3 & G4 & G5 & _). pose proof (ext_facts s OK ch Hin) as (E1 & E2 & E3 & _).
    acb. unfold AIMG_TOP in E1. tlia.
  Qed.
  (* [comment removed for export] *)
  Lemma batch_size_bound : forall b, In b (qc_list (as_tq st) ++ qc_list (as_gq st)) -> kBatchSize <= qb_size b <= kBatchSize + kBatchCount * 2^47.
  Proof.
    intros b Hb. pose proof (WF_batch st b WFs Hb) as (CNT & CB & _ & _ & _ & _ & _ & SZ & _). rewrite SZ.
    assert (SUM : forall qs, 0 <= fold_right (fun (q : Z) (acc : Z) => match find_chunk (as_chunks st) (q + kChunkHeaderSize) with Some c => ch_used c | None => 0 end + acc) 0 qs
                            <= zlen qs * 2^47).
    { induction qs as [|q qs IH]; [unfold zlen; cbn; tlia|]. cbn [fold_right]. rewrite zlen_cons.
      assert (T : 0 <= match find_chunk (as_chunks st) (q + kChunkHeaderSize) with Some c => ch_used c | None => 0 end < 2^47).
      { destruct (find_chunk (as_chunks st) (q + kChunkHeaderSize)) as [c|] eqn:F; [| tlia]. pose proof (used_lt47 c (find_chunk_In _ _ _ F)). tlia. }
      tlia. }
    specialize (SUM (qb_chunks b)). rewrite <- CNT in SUM. unfold kBatchCount in *. tlia.
  Qed.
  (* [comment removed for export] *)
  Lemma batches_len_bound : zlen (qc_list (as_tq st) ++ qc_list (as_gq st)) <= 458752.
  Proof.
    set (L := qc_list (as_tq st) ++ qc_list (as_gq st)).
    set (idx := fun b : qbatch => Z.to_nat ((qb_addr b - region_beg st kBatchClass) / 8192)).
    assert (CVb : forall b, In b L -> exists q, 0 <= q < 458752 /\ qb_addr b = region_beg st kBatchClass + 8192 * q).
    { intros b Hb. pose proof (batch_carved s OK b Hb) as (CV & _). pose proof (carved_range st _ _ WFs CV) as (C1 & C2 & _).
      destruct CV as (_ & _ & C3 & C4 & C5). change (class_size kBatchClass) with 8192 in *. unfold kFreeArrayOffset in C2.
      exists ((qb_addr b - region_beg st kBatchClass) / 8192). clear - C1 C2 C3 C4 C5. unfold st in *. Z.div_mod_to_equations. tlia. }
    assert (ND : List.NoDup (map idx L)).
    { apply (NoDup_map_transfer qb_addr idx L (batch_addrs_nodup s OK)). intros x y Hx Hy E.
      destruct (CVb x Hx) as (qx & Qx & Ex). destruct (CVb y Hy) as (qy & Qy & Ey). subst idx. cbn in E. rewrite Ex, Ey in E |- *.
      replace (region_beg st kBatchClass + 8192 * qx - region_beg st kBatchClass) with (qx * 8192) in E by tlia.
      replace (region_beg st kBatchClass + 8192 * qy - region_beg st kBatchClass) with (qy * 8192) in E by tlia.
      rewrite !Z.div_mul in E by tlia. apply Z2Nat.inj in E; tlia. }
    assert (INCL : incl (map idx L) (seq 0 (Z.to_nat 458752))).
    { intros n Hn. apply in_map_iff in Hn. destruct Hn as (b & E & Hb). destruct (CVb b Hb) as (q & Q & Eb). subst n idx. cbn. rewrite Eb.
      replace (region_beg st kBatchClass + 8192 * q - region_beg st kBatchClass) with (q * 8192) by tlia. rewrite Z.div_mul by tlia.
      apply in_seq. clear - Q. tlia. }
    pose proof (NoDup_incl_length ND INCL) as LEN. rewrite length_map, length_seq in LEN. clear - LEN. unfold zlen. tlia.
  Qed.
End Bounds.

Section FreeApp.
  Context {HCEIL : HeapCeil}.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (s : ast) (LB : list (Z * Z)) (d : depot) (lo : Z) (CH : list (Z * Z)) (ch : chunk) (bs sbs : list byte).

  Let st := a_st s.
  Let TH := a_thr s.
  Let CTX := a_ctx s.
  Let sb := a_sb s.
  Let U := ch_user_beg ch.
  Let size := ch_used ch.
  Let tq := as_tq st.
  Let l := qc_list tq.
  Let k := zlen l.
  Let lb := last l (mkQB 0 0 0 []).
  Let LA := qb_addr lb.
  Let lcount := qb_count lb.
  Let CHI := icpt_chain (bv_unsigned ra) (bv_unsigned s0) (bv_unsigned sp) (a_top s) CH.
  Let T := utrace 0x1bf2bc (bv_unsigned sp) (a_top s) (a_bot s) 30 CHI.
  Let nT := Z.of_nat (length T).
  Let d' := d_put d (depot_hash T) nT.
  (* [comment removed for export] *)
  Let tq' := tq_app tq (ch_chunk_beg ch) size.
  Let lb' := mkQB LA (qb_size lb + size) (lcount + 1) (qb_chunks lb ++ [ch_chunk_beg ch]).
  Let s' := free_s' s ch tq' (as_cache st) (a_L s) (a_S s) (a_AL s).
  (* [comment removed for export] *)
  Let Wh : list ivl := free_head_W lo (bv_unsigned sp) TH U size d.
  Let Wa : list ivl := [(lo, bv_unsigned sp + -2208); (TH + OT_TQ + 24, TH + OT_TQ + 32); (LA + 8, LA + 24); (LA + 24 + 8 * lcount, LA + 32 + 8 * lcount)].
  Let W : list ivl := Wh ++ Wa.

  Hypothesis HR : ARHEAP s LB m.
  Hypothesis CHIN : In ch (chunk_list st).
  Hypothesis ALLOC : ch_state ch = CAllocated.
  Hypothesis DEP : DEPOT asegs d m.
  Hypothesis DPL : depot_placed s d.
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : aceil <= lo.
  Hypothesis HI : lo + 2944 <= bv_unsigned sp.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPT : bv_unsigned sp + 16 <= 2^47.
  Hypothesis TP : tp = wz ATP.
  Hypothesis DLO : d_nb d + 16 * 65536 <= lo /\ d_sb d + 8 * 131072 <= lo.
  Hypothesis DCAP : d_ids d + 1 < 65536 /\ d_frames d + 31 <= 131072.
  Hypothesis FCH : goodframe (a_bot s) (bv_unsigned sp) (a_top s) = true -> goodframe (bv_unsigned sp) (bv_unsigned s0) (a_top s) = true ->
                   bv_unsigned sp + 16 <= bv_unsigned s0 /\ frame_chain asegs m (a_top s) (bv_unsigned s0) CH.
  Hypothesis Ha0 : a0 = wz U.
  (* [comment removed for export] *)
  Hypothesis BLK : rw_cells asegs m U [CB (Z.to_nat size) bs].
  Hypothesis SHB : SHAD m U sbs /\ Z.of_nat (length sbs) = nsh size.
  (* [comment removed for export] *)
  Hypothesis QSZ : size <= kQuarantineMaxSize /\ size < 2^32.
  Hypothesis NN : l <> [] /\ lcount < kBatchCount.
  Hypothesis NOD : qc_bytes tq + size <= kMaxCacheSize.
  (* [comment removed for export] *)
  Hypothesis UHI : aapp (ch_user_beg ch - 16) (16 + round_up (ch_used ch) 8).   (* [comment removed for export] *)

  Let R : AREP s m. Proof. exact (proj1 HR). Qed.
  Let OK : ast_ok s. Proof. exact (proj1 R). Qed.
  Let PL : placed_ok s. Proof. exact (proj1 OK). Qed.
  Let WFs : WF st. Proof. exact (proj2 OK). Qed.
  (* [comment removed for export] *)
  Let FLG4 : rw_cells asegs m AIAINIT [C1 (b8 (if as_internal_init st then 1 else 0)); C1 (b8 0); C2 (wz 0)].
  Proof.
    pose proof R as RR. destruct RR as (_ & _ & FL & _).
    destruct FL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F16 & _). exact F16.
  Qed.
  Let IAX : if as_internal_init st then ia_after m else ia_pristine m.
  Proof. pose proof R as RR. destruct RR as (_ & _ & _ & _ & _ & IA & _). unfold ia_rep in IA. unfold ia_after, ia_pristine. exact IA. Qed.
  Let PURE := free_pure s m ch R CHIN UHI.
  Let EXT : ch_lo ch <= U - 16 /\ U + round_up size 8 <= ch_end ch /\ U + 8 <= ch_end ch /\ 12599296 <= ch_lo ch /\ ch_end ch <= aceil
            /\ ch_lo ch mod 8 = 0 /\ ch_end ch mod 8 = 0 /\ ch_alloc_beg ch + ch_rz ch = U /\ 16 <= ch_rz ch /\ ch_lo ch <= ch_alloc_beg ch.
  Proof.
    pose proof (record_ext s OK ch CHIN) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9).
    pose proof (chunk_geom s OK ch CHIN) as (G1 & G2 & G3 & G4 & G5 & G6 & _).
    pose proof (record_band s OK ch CHIN) as RB. unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AIMG_TOP, AHI_LO in RB. unfold AHI_LO in UHI.
    clear - X1 X2 X3 X4 X5 X6 X7 X8 X9 G1 G2 G3 G4 G5 G6 RB UHI. subst U size. pose proof (aapp_env _ _ UHI ltac:(clear - G3 G5; tlia)) as [UE _]. unfold AHI_LO, AIMG_TOP in *. repeat split; try assumption; tlia.
  Qed.
  Let LAST := free_last_cells s m ch d R CHIN DPL (proj1 NN).

  (* [comment removed for export] *)
  Let BND : aceil <= lo /\ 4096 <= TH /\ TH + 4096 <= aceil /\ 12599296 <= CTX /\ CTX + 160 <= aceil
            /\ 0x10007fff8000 <= sb /\ sb + 137438953472 + 4096 <= aceil /\ 12599296 <= a_pa s /\ a_pa s + 8388608 <= aceil
            /\ 12599296 <= d_nb d /\ d_nb d + 16 * 65536 <= aceil /\ 12599296 <= d_sb d /\ d_sb d + 8 * 131072 <= aceil
            /\ 12599312 <= U /\ U + round_up size 8 <= aceil /\ 1 <= size /\ size <= round_up size 8 /\ round_up size 8 = 8 * nsh size
            /\ 0x10007fff8000 <= LA /\ LA + 8192 <= aceil /\ 1 <= lcount <= 1020
            /\ 2148314624 <= sh U /\ sh U + nsh size <= 0x10007fff8000 /\ U mod 16 = 0 /\ lo + 2944 <= bv_unsigned sp.   (* [comment removed for export] *)
  Proof.
    pose proof PURE as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & X1 & X2 & X3 & _).
    pose proof LAST as (_ & _ & _ & _ & _ & CNB & _ & L1 & L2 & _).
    pose proof PL as (_ & _ & _ & P1 & P2 & P3 & _). pose proof DPL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & N1 & N2 & N3 & N4).
    pose proof (proj2 NN) as NN2.
    apply aapp_env in P2; [| unfold kPtrArrayReserve; clear; tlia]. apply aapp_env in N1; [| clear; tlia]. apply aapp_env in N3; [| clear; tlia].
    clear - Z1 Z2 Z3 Z4 Z5 Z6 Y1 Y2 Y4 Y5 X1 X2 CNB L1 L2 P2 P3 N1 N2 N3 N4 LO NN2 HI.
    subst U size LA lcount lb l tq TH CTX sb st. unfold AHI_LO, AIMG_TOP, kSpaceSize, kPageSize, kPtrArrayReserve, kBatchSize, kBatchCount in *.
    destruct Z2 as (ZA & _ & ZB). unfold aapp, aapp_lo, aapp_hi, AIMG_TOP, ALOWSH_LO, AHI_LO in ZA, ZB.   (* [comment removed for export] *)
    assert (SH : 2148314624 <= sh (ch_user_beg ch) /\ sh (ch_user_beg ch) + nsh (ch_used ch) <= 0x10007fff8000).
    { acb. clear - ZA Z3 Z6 Z1 ACEILB. unfold sh, ASHADOW_BASE. Z.div_mod_to_equations. tlia. }
    clear ZA. repeat match goal with |- _ /\ _ => split end; try tlia.
  Qed.

  (* [comment removed for export] *)
  Let BANDS : hidden ((TH + 4096 <= 65536 \/ (12599296 <= TH /\ TH + 4096 <= 2147446784) \/ 17594333495296 <= TH)
                   /\ (CTX + 160 <= 2147446784 \/ 17594333495296 <= CTX)
                   /\ (a_pa s + 8388608 <= 2147446784 \/ 17594333495296 <= a_pa s)
                   /\ (d_nb d + 16 * 65536 <= 2147446784 \/ 17594333495296 <= d_nb d)
                   /\ (d_sb d + 8 * 131072 <= 2147446784 \/ 17594333495296 <= d_sb d)).
  Proof.
    pose proof PL as (_ & _ & _ & _ & P2 & _ & _ & T2 & _ & _ & X2 & _). pose proof DPL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & N1 & _ & N3 & _).
    fold TH in T2. fold CTX in X2.
    split. split; [exact (akobj_lit _ _ T2)|]. split; [exact (aapp_lit _ _ X2)|].
    split; [pose proof (aapp_lit _ _ P2) as L; unfold kPtrArrayReserve in L; exact L|].
    split; [exact (aapp_lit _ _ N1)| exact (aapp_lit _ _ N3)].
  Qed.
  Tactic Notation "bands_as" simple_intropattern(p) := (let X := fresh "BX" in pose proof BANDS as X; destruct X as [p]).
  (* [comment removed for export] *)
  Let UBANDS : hidden ((sh U + nsh size <= U - 16 \/ U + round_up size 8 <= sh U)
                    /\ (U + round_up size 8 <= 2147446784 \/ 17594333495296 <= U - 16)
                    /\ (ch_end ch <= 2147446784 \/ 17594333495296 <= ch_lo ch)).
  Proof.
    pose proof PURE as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & _). pose proof (record_band s OK ch CHIN) as RBB. destruct Z2 as (ZA & _).
    clear - Z1 ZA Z3 Z5 Z6 RBB. constructor. subst U size. unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AIMG_TOP, AHI_LO in ZA, RBB. acb.
    split; [| clear - ZA RBB; tlia]. clear - ZA Z3 Z6 Z1 ACEILB. unfold sh, ASHADOW_BASE. Z.div_mod_to_equations. tlia.
  Qed.
  Tactic Notation "ubands_as" simple_intropattern(p) := (let X := fresh "UBX" in pose proof UBANDS as X; destruct X as [p]).

  Ltac wsplit := unfold W, Wh, Wa, free_head_W; cbn [outside depot_W app]; repeat split; try exact I.
  (* [comment removed for export] *)
  Ltac zlets := repeat match goal with H := _ |- _ => subst H end.
  Ltac zfin := zlets; unfold AHI_LO, AIMG_TOP, ALOWSH_LO, OT_TQ, OT_CACHE, a_sb, a_ri, disj, kPageSize, kBatchSize, kSpaceSize, kPtrArrayReserve in *; tlia.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma Z_core : forall a, a < aceil -> ~ (AIAINIT <= a < AIAINIT + 4) -> ~ (AIAINST <= a < AIAINST + 0x81030) ->
    ~ (7915480 <= a < 12109808) -> ~ (7849928 <= a < 7849956) ->
    ~ (U - 16 <= a < U - 12) -> ~ (U <= a < U + 8) -> ~ (TH + 104 <= a < TH + 112) -> ~ (TH + 2800 <= a < TH + 3169) ->
    ~ (sh U <= a < sh U + nsh size) -> ~ (LA + 8 <= a < LA + 8192) ->
    ~ (d_nb d <= a < d_nb d + 16 * 65536) -> ~ (d_sb d <= a < d_sb d + 8 * 131072) -> outside W a.
  Proof.
    intros a Ha N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 N12. pose proof BND as B. clear - Ha N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 N12 B.
    wsplit; unfold AIAINIT, AIAINST, OT_TQ in *; tlia.
  Qed.
  (* [comment removed for export] *)
  Lemma Z_stat : forall a, 65536 <= a < AIMG_TOP -> ~ (AIAINIT <= a < AIAINIT + 4) -> ~ (AIAINST <= a < AIAINST + 0x81030) ->
    ~ (7915480 <= a < 12109808) -> ~ (7849928 <= a < 7849956) -> outside W a.
  Proof.
    intros a Ha N1 N2 N3 N4. pose proof BND as B. bands_as (BT & _). apply Z_core; try assumption; clear - Ha B BT; unfold AIMG_TOP, AHI_LO in *; acb; try tlia.
    all: unfold sh, ASHADOW_BASE; Z.div_mod_to_equations; tlia.
  Qed.
  (* [comment removed for export] *)
  Lemma Z_hi : forall a, (AIMG_TOP <= a < ALOWSH_LO \/ AHI_LO <= a < aceil) -> ~ (U - 16 <= a < U - 12) -> ~ (U <= a < U + 8) -> ~ (TH + 104 <= a < TH + 112) ->
    ~ (TH + 2800 <= a < TH + 3169) -> ~ (LA + 8 <= a < LA + 8192) -> ~ (d_nb d <= a < d_nb d + 16 * 65536) -> ~ (d_sb d <= a < d_sb d + 8 * 131072) ->
    outside W a.
  Proof.
    intros a Ha N1 N2 N3 N4 N5 N6 N7. pose proof BND as B. apply Z_core; try assumption; clear - Ha B; unfold AIAINIT, AIAINST, AIMG_TOP, ALOWSH_LO, AHI_LO in *; acb; tlia.
  Qed.
  (* [comment removed for export] *)
  Lemma Z_sh : forall a, ASHADOW_BASE <= a < AHI_LO -> ~ (sh U <= a < sh U + nsh size) -> outside W a.
  Proof.
    intros a Ha N1. pose proof BND as B. bands_as (BT & _ & _ & BN & BS). ubands_as (_ & UB & _). apply Z_core; try assumption; clear - Ha B BT BN BS UB;
      unfold AIAINIT, AIAINST, AHI_LO, ASHADOW_BASE in *; acb; tlia.
  Qed.
  (* [comment removed for export] *)
  Lemma Z_thr : forall a, TH <= a < TH + 4096 -> ~ (TH + 104 <= a < TH + 112) -> ~ (TH + 2800 <= a < TH + 3169) -> outside W a.
  Proof.
    intros a Ha N1 N2. pose proof BND as B. bands_as (BT & _). pose proof LAST as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LT & _).
    pose proof (free_plu s m ch d R CHIN DPL) as (PU & _). pose proof DPL as (G1 & G2 & _). fold TH in G1, G2.
    apply Z_core; try assumption; clear - Ha N1 N2 B BT LT PU G1 G2; unfold AIAINIT, AIAINST, disj, kPageSize, kBatchSize in *; zlets; acb; try tlia.
    all: unfold sh, ASHADOW_BASE; Z.div_mod_to_equations; tlia.
  Qed.
  (* [comment removed for export] *)
  Lemma Z_static : forall a, astatic a -> ~ (AIAINIT <= a < AIAINIT + 4) -> ~ (AIAINST <= a < AIAINST + 0x81030) -> outside W a.
  Proof.
    intros a Ha N1 N2. apply Z_stat; [| exact N1| exact N2| |]; clear - Ha; unfold astatic in Ha;
    unfold AINST, OI_MISMATCH, AFLAGS, ACFLAGS, ASHBASE_CELL, AHIGHMEMEND, ACANPOISON, AINITED, AALLOCFLAGS, AIAINIT, AHOOKS, AREALMEMSET,
           AIAINST, AGOT_LO, APAGESZ, ASECNAME, APRIMNAME, ATLSSLOT, ATSD, ALSANDIS, AGOT2, AIMG_TOP in *; tlia.
  Qed.
  Lemma Z_flags : forall a, aflags_range a -> ~ (AIAINIT <= a < AIAINIT + 4) -> ~ (AIAINST <= a < AIAINST + 0x81030) -> outside W a.
  Proof.
    intros a Ha N1 N2. apply Z_stat; [| exact N1| exact N2| |]; clear - Ha; unfold aflags_range in Ha;
    unfold AFLAGS, ACFLAGS, ASHBASE_CELL, AHIGHMEMEND, ACANPOISON, AINITED, ACTXSIZE, ATSDINIT, AALLOCFLAGS, AIAINIT, AHOOKS, ADYING,
           AREALMEMSET, AIAINST, AGOT_LO, APAGESZ, ASECNAME, APRIMNAME, ATLSSLOT, ATSD, ALSANDIS, AGOT2, AIMG_TOP in *; tlia.
  Qed.
  (* [comment removed for export] *)
  Lemma Z_SH : forall lo' kk a, 0 <= lo' -> lo' mod 8 = 0 -> 0 <= kk -> lo' + 8 * kk <= aceil ->
    (lo' + 8 * kk <= U \/ U + round_up size 8 <= lo') -> sh lo' <= a < sh lo' + kk -> outside W a.
  Proof.
    intros lo' kk a H0 H8 Hk Hhi Hd Ha. pose proof BND as B.
    assert (U8 : U mod 8 = 0) by (clear - B; Z.div_mod_to_equations; tlia).
    assert (SS : sh lo' + kk <= sh U \/ sh U + nsh size <= sh lo').
    { apply sh_sep; try assumption; clear - B Hd; tlia. }
    assert (SB : 0x7fff8000 <= sh lo' /\ sh lo' + kk <= 0x10007fef8000) by (clear - H0 Hk Hhi; acb; unfold sh, ASHADOW_BASE; Z.div_mod_to_equations; tlia).
    apply Z_sh; [unfold ASHADOW_BASE, AHI_LO| ]; clear - Ha SS SB; tlia.
  Qed.
  (* [comment removed for export] *)
  Lemma Z_rec_other : forall x a, In x (chunk_list st) -> x <> ch -> ch_lo x <= a < ch_end x -> outside W a.
  Proof.
    intros x a Hx NE Ha. pose proof BND as B.
    pose proof (record_ext s OK x Hx) as (X1 & X2 & _). pose proof (record_vs_record s OK ch CHIN x Hx NE) as D. pose proof EXT as (E1 & _ & E3 & _).
    pose proof (rec_vs_thread s m x R Hx) as RT. pose proof (rec_vs_depot s m x d R Hx DPL) as [RD1 RD2].
    pose proof LAST as (_ & _ & _ & INlb & _). pose proof (batch_vs_record s OK x Hx lb INlb) as BL. fold LA in BL.
    pose proof (record_band s OK x Hx) as RBx. unfold aapp, aapp_lo, aapp_hi in RBx.
    apply Z_hi; unfold AHI_LO, AIMG_TOP, ALOWSH_LO, kPageSize, kBatchSize in *; clear - Ha B X1 X2 D E1 E3 RT RD1 RD2 BL RBx; tlia.
  Qed.
  Lemma Z_rec_self : forall a, ch_lo ch <= a < ch_end ch -> ~ (U - 16 <= a < U - 12) -> ~ (U <= a < U + 8) -> outside W a.
  Proof.
    intros a Ha N1 N2. pose proof BND as B. pose proof EXT as (E1 & E2 & E3 & E4 & E5 & _).
    pose proof (rec_vs_thread s m ch R CHIN) as RT. pose proof (rec_vs_depot s m ch d R CHIN DPL) as [RD1 RD2].
    pose proof LAST as (_ & _ & _ & INlb & _). pose proof (batch_vs_record s OK ch CHIN lb INlb) as BL. fold LA in BL.
    ubands_as (_ & _ & UC). apply Z_hi; unfold AHI_LO, AIMG_TOP, ALOWSH_LO, kPageSize, kBatchSize in *; clear - Ha N1 N2 B E4 E5 RT RD1 RD2 BL UC; tlia.   (* [comment removed for export] *)
  Qed.
  Lemma Z_rec_self_sh : forall a, sh (ch_lo ch) <= a < sh (ch_end ch) -> ~ (sh U <= a < sh U + nsh size) -> outside W a.
  Proof.
    intros a Ha N1. pose proof EXT as (_ & _ & _ & E4 & E5 & _). apply Z_sh; [| exact N1].
    clear - Ha E4 E5. acb. unfold AHI_LO, sh in *. unfold ASHADOW_BASE in *. Z.div_mod_to_equations. tlia.
  Qed.
  Lemma Z_rec_other_sh : forall x lo' kk a, In x (chunk_list st) -> x <> ch -> ch_lo x <= lo' -> lo' + 8 * kk <= ch_end x -> lo' mod 8 = 0 -> 0 <= kk ->
    sh lo' <= a < sh lo' + kk -> outside W a.
  Proof.
    intros x lo' kk a Hx NE G1 G2 G3 G4 Ha. pose proof (record_ext s OK x Hx) as (X1 & X2 & _).
    pose proof (record_vs_record s OK ch CHIN x Hx NE) as D. pose proof EXT as (E1 & E2 & _).
    apply (Z_SH lo' kk a); try assumption.
    - clear - G1 X1. unfold AIMG_TOP in X1. tlia.
    - clear - G2 X2. tlia.
    - clear - G1 G2 D E1 E2. tlia.
  Qed.
  (* [comment removed for export] *)
  Lemma Z_batch : forall b a, In b (qc_list (as_tq st) ++ qc_list (as_gq st)) -> qb_addr b <> LA -> qb_addr b <= a < qb_addr b + kBatchSize -> outside W a.
  Proof.
    intros b a Hb NE Ha. pose proof BND as B. pose proof (batch_carved s OK b Hb) as (CV & _).
    pose proof (batch_in_space s OK b Hb) as (P1 & P2 & _). pose proof (batch_vs_record s OK ch CHIN b Hb) as D. pose proof EXT as (E1 & _ & E3 & _).
    pose proof LAST as (_ & _ & _ & INlb & _). pose proof (carved_vs_batch s OK _ _ CV lb INlb ltac:(hci; fold LA; clear - NE; congruence)) as BL. fold LA in BL.
    pose proof (carved_vs_thread s OK _ _ CV) as CT. pose proof (carved_vs_depot s OK _ _ CV d DPL) as [CD1 CD2].
    change (class_size kBatchClass) with 8192 in *. fold sb in P1, P2.
    apply Z_hi; unfold AHI_LO, AIMG_TOP, ALOWSH_LO, kPageSize, kBatchSize, kSpaceSize in *; clear - Ha B P1 P2 D E1 E3 BL CT CD1 CD2; tlia.
  Qed.
  Lemma Z_batch_sh : forall b a, In b (qc_list (as_tq st) ++ qc_list (as_gq st)) -> sh (qb_addr b) <= a < sh (qb_addr b) + kBatchSize / 8 -> outside W a.
  Proof.
    intros b a Hb Ha. pose proof BND as B. pose proof (batch_in_space s OK b Hb) as (P1 & P2 & P3). pose proof (batch_vs_record s OK ch CHIN b Hb) as D.
    pose proof EXT as (E1 & E2 & _). fold sb in P1, P2.
    apply (Z_SH (qb_addr b) 1024 a); unfold kBatchSize, kSpaceSize in *; try (clear - Ha B P1 P2 P3 D E1 E2; acb; tlia).
  Qed.
  Lemma Z_freech : forall c0 cp a, 0 <= c0 < kNumClasses -> In cp (rg_free_array (get_region st c0)) \/ In cp (pc_chunks (get_pc st c0)) ->
    compact_to_addr st c0 cp <= a < compact_to_addr st c0 cp + class_size c0 -> outside W a.
  Proof.
    intros c0 cp a Hc0 Hin Ha. pose proof BND as B.
    pose proof (freech_in_space s OK c0 cp Hc0 Hin) as (P1 & P2 & P3 & P4 & P5). pose proof (freech_vs_record s OK ch CHIN c0 cp Hc0 Hin) as D.
    pose proof EXT as (E1 & _ & E3 & _). pose proof LAST as (_ & _ & _ & INlb & _).
    assert (CV : carved st c0 (compact_to_addr st c0 cp)) by (destruct Hin; [apply carved_free| apply carved_cache]; assumption).
    pose proof (carved_vs_batch s OK _ _ CV lb INlb ltac:(hci; apply (batch_not_free s OK lb c0 cp INlb Hc0 Hin))) as BL. fold LA in BL.
    pose proof (carved_vs_thread s OK _ _ CV) as CT. pose proof (carved_vs_depot s OK _ _ CV d DPL) as [CD1 CD2].
    apply Z_hi; clear - Ha B P1 P2 D E1 E3 BL CT CD1 CD2; zfin.
  Qed.
  Lemma Z_freech_sh : forall c0 cp a, 0 <= c0 < kNumClasses -> In cp (rg_free_array (get_region st c0)) \/ In cp (pc_chunks (get_pc st c0)) ->
    sh (compact_to_addr st c0 cp) <= a < sh (compact_to_addr st c0 cp) + class_size c0 / 8 -> outside W a.
  Proof.
    intros c0 cp a Hc0 Hin Ha. pose proof BND as B.
    pose proof (freech_in_space s OK c0 cp Hc0 Hin) as (P1 & P2 & P3 & P4 & P5). pose proof (freech_vs_record s OK ch CHIN c0 cp Hc0 Hin) as D.
    pose proof EXT as (E1 & E2 & _).
    assert (C8 : 8 * (class_size c0 / 8) = class_size c0) by (clear - P5; Z.div_mod_to_equations; tlia).
    apply (Z_SH (compact_to_addr st c0 cp) (class_size c0 / 8) a); clear - Ha B P1 P2 P3 P4 D E1 E2 C8; acb; zfin.
  Qed.
  Lemma Z_farray : forall c0 a, 0 <= c0 < kNumClasses -> FA s c0 <= a < FA s c0 + rg_mapped_free_array (get_region st c0) -> outside W a.
  Proof.
    intros c0 a Hc0 Ha. pose proof BND as B.
    pose proof (farray_in_space s OK c0 Hc0) as (P1 & P2 & P3 & P4 & P5). pose proof (farray_vs_record s OK ch CHIN c0 Hc0) as D.
    pose proof EXT as (E1 & _ & E3 & _). pose proof LAST as (_ & _ & _ & INlb & _). pose proof (batch_carved s OK lb INlb) as (CV & _).
    pose proof (carved_vs_farray s OK _ _ CV c0 Hc0) as BL. fold LA in BL. change (class_size kBatchClass) with 8192 in BL.
    pose proof PL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & D2 & _). pose proof DPL as (_ & _ & G3 & G4 & _).
    apply Z_hi; clear - Ha B P1 P2 D E1 E3 BL D2 G3 G4; zfin.
  Qed.
  Lemma Z_farray_sh : forall c0 a, 0 <= c0 < kNumClasses -> sh (FA s c0) <= a < sh (FA s c0) + rg_mapped_free_array (get_region st c0) / 8 -> outside W a.
  Proof.
    intros c0 a Hc0 Ha. pose proof BND as B.
    pose proof (farray_in_space s OK c0 Hc0) as (P1 & P2 & P3 & P4 & P5). pose proof (farray_vs_record s OK ch CHIN c0 Hc0) as D.
    pose proof EXT as (E1 & E2 & _).
    apply (Z_SH (FA s c0) (rg_mapped_free_array (get_region st c0) / 8) a); clear - Ha B P1 P2 P3 P4 P5 D E1 E2; acb;
      (zfin || (unfold kSpaceSize, sb, st in *; Z.div_mod_to_equations; tlia)).
  Qed.
  Lemma Z_tail : forall c0 a, 0 <= c0 < kNumClasses ->
    RB s c0 + rg_allocated_user (get_region st c0) <= a < RB s c0 + rg_mapped_user (get_region st c0) -> outside W a.
  Proof.
    intros c0 a Hc0 Ha. pose proof BND as B.
    pose proof (tail_in_space s OK c0 Hc0) as (P1 & P2 & P3 & P4 & P5). pose proof (tail_vs_record s OK ch CHIN c0 Hc0) as D.
    pose proof EXT as (E1 & _ & E3 & _). pose proof LAST as (_ & _ & _ & INlb & _). pose proof (batch_carved s OK lb INlb) as (CV & _).
    pose proof (carved_vs_tail s OK _ _ CV c0 Hc0) as BL. fold LA in BL. change (class_size kBatchClass) with 8192 in BL.
    pose proof PL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & D2 & _). pose proof DPL as (_ & _ & G3 & G4 & _).
    apply Z_hi; clear - Ha B P1 P2 D E1 E3 BL D2 G3 G4; zfin.
  Qed.
  Lemma Z_tail_sh : forall c0 a, 0 <= c0 < kNumClasses ->
    sh (RB s c0 + rg_allocated_user (get_region st c0)) <= a
      < sh (RB s c0 + rg_allocated_user (get_region st c0)) + (rg_mapped_user (get_region st c0) - rg_allocated_user (get_region st c0)) / 8 -> outside W a.
  Proof.
    intros c0 a Hc0 Ha. pose proof BND as B.
    pose proof (tail_in_space s OK c0 Hc0) as (P1 & P2 & P3 & P4 & P5). pose proof (tail_vs_record s OK ch CHIN c0 Hc0) as D.
    pose proof EXT as (E1 & E2 & _).
    apply (Z_SH (RB s c0 + rg_allocated_user (get_region st c0)) ((rg_mapped_user (get_region st c0) - rg_allocated_user (get_region st c0)) / 8) a);
      clear - Ha B P1 P2 P3 P4 P5 D E1 E2; acb; (zfin || (unfold kSpaceSize, sb, st in *; Z.div_mod_to_equations; tlia)).
  Qed.
  Lemma Z_rinfo : forall a, a_ri s <= a < a_ri s + kPageSize -> outside W a.
  Proof.
    intros a Ha. pose proof BND as B. pose proof (rinfo_vs_record s OK ch CHIN) as D. pose proof EXT as (E1 & _ & E3 & _).
    pose proof LAST as (_ & _ & _ & INlb & _). pose proof (batch_carved s OK lb INlb) as (CV & _). pose proof (carved_vs_rinfo s OK _ _ CV) as BL.
    fold LA in BL. change (class_size kBatchClass) with 8192 in BL.
    pose proof PL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & D2 & _). pose proof DPL as (_ & _ & G3 & G4 & _).
    unfold a_ri in *. apply Z_hi; clear - Ha B D E1 E3 BL D2 G3 G4; unfold a_sb in *; zfin.
  Qed.
  Lemma Z_pa : forall a, a_pa s <= a < a_pa s + kPtrArrayReserve -> outside W a.
  Proof.
    intros a Ha. pose proof BND as B. pose proof EXT as (E1 & _ & E3 & _).
    pose proof LAST as (_ & _ & _ & INlb & _). pose proof (batch_carved s OK lb INlb) as (CV & _). pose proof (carved_vs_pa s OK _ _ CV) as BL.
    fold LA in BL. change (class_size kBatchClass) with 8192 in BL.
    pose proof PL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & D1 & D2 & D3 & D4 & _). pose proof DPL as (_ & _ & _ & _ & _ & _ & G7 & G8 & _).
    assert (RP : a_pa s + kPtrArrayReserve <= ch_lo ch \/ ch_end ch <= a_pa s).
    { destruct (ch_primary ch) eqn:E.
      - pose proof (record_primary_space s OK ch CHIN E) as [Q1 Q2]. clear - Q1 Q2 D1. unfold a_sb, disj, kSpaceSize, kPageSize in *. tlia.
      - destruct (record_secondary_map s OK ch CHIN E) as (h & Hh & L0 & E0 & _).
        pose proof PL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SEC & _).
        pose proof (SEC h Hh) as (_ & _ & _ & _ & _ & Q & _). clear - L0 E0 Q. unfold disj in *. tlia. }
    bands_as (_ & _ & BP & _). apply Z_hi; clear - Ha B E1 E3 BL D4 G7 G8 RP BP; zfin.
  Qed.
  Lemma Z_sechdr : forall h a, In h (as_sec st) -> sc_map_beg h <= a < sc_map_beg h + kPageSize -> outside W a.
  Proof.
    intros h a Hh Ha. pose proof BND as B. pose proof EXT as (E1 & _ & E3 & _ & _ & _ & _ & E8 & E9 & E10).
    pose proof LAST as (_ & _ & _ & INlb & _). pose proof (batch_carved s OK lb INlb) as (CV & _). pose proof (carved_vs_sec s OK _ _ CV h Hh) as BL.
    fold LA in BL. change (class_size kBatchClass) with 8192 in BL.
    pose proof PL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SEC & SEC2 & _).
    pose proof (SEC h Hh) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9). pose proof DPL as (_ & _ & _ & _ & _ & _ & _ & _ & G9 & _). destruct (G9 h Hh) as [Gh1 Gh2].
    unfold aapp, aapp_lo, aapp_hi in Q2.   (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (RP : sc_map_beg h + kPageSize <= U - 16 \/ U + 8 <= sc_map_beg h).
    { destruct (ch_primary ch) eqn:E.
      - pose proof (sechdr_vs_primary_record s OK ch CHIN h Hh E) as D. clear - D E1 E3. tlia.
      - destruct (record_secondary_map s OK ch CHIN E) as (h0 & Hh0 & L0 & E0 & A0).
        destruct (Z.eq_dec (sc_map_beg h) (sc_map_beg h0)) as [EQ|NE].
        + left. rewrite EQ. clear - A0 E8 E9. tlia.
        + pose proof (SEC2 h h0 Hh Hh0 NE) as D. clear - D L0 E0 E1 E3 Q4. unfold disj, kPageSize in *. tlia. }
    apply Z_hi; clear - Ha B Q2 Q3 Q4 Q7 BL Gh1 Gh2 RP; zfin.
  Qed.
  Lemma Z_thr1 : forall a, TH <= a < TH + OT_TQ -> outside W a.
  Proof. intros a Ha. apply Z_thr; clear - Ha; unfold OT_TQ in *; tlia. Qed.
  Lemma Z_thr2 : forall a, TH + OT_TQ + 32 <= a < TH + OT_CACHE -> outside W a.
  Proof. intros a Ha. apply Z_thr; clear - Ha; unfold OT_TQ, OT_CACHE in *; tlia. Qed.
  Lemma Z_thr3 : forall a, TH + OT_CACHE <= a < TH + 2800 -> outside W a.
  Proof. intros a Ha. apply Z_thr; clear - Ha; unfold OT_CACHE in *; tlia. Qed.
  Lemma Z_ctx : forall a, CTX + 8 <= a < CTX + 160 -> outside W a.
  Proof. intros a Ha. pose proof BND as B. pose proof PURE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Y6 & _).
         pose proof (free_plu s m ch d R CHIN DPL) as (_ & PU & _). pose proof DPL as (_ & _ & _ & _ & G5 & G6 & _).
         pose proof LAST as (_ & _ & _ & INlb & _). pose proof (batch_carved s OK lb INlb) as (CV & _). pose proof (carved_vs_ctx s OK _ _ CV) as BL.
         change (class_size kBatchClass) with 8192 in BL. bands_as (_ & BC & _).
         apply Z_hi; clear - Ha B Y6 PU G5 G6 BL BC; zfin. Qed.

  (* [comment removed for export] *)
  Section Post.
    Variables (m' : mem) (b1 actx : Z).
    Let idv := d_putid d (depot_hash T).
    Let P := outside W.
    Hypothesis MU : munch W m m'.
    Hypothesis WM : wmono asegs m m'.
    Hypothesis B1 : 0 <= b1 < 256 /\ (b1 mod 128 = 17 \/ b1 mod 128 = 65).
    Hypothesis HDR' : rw_cells asegs m' (U + -16) [C1 (b8 3); C1 (b8 b1); C2 (wz 0); C4 (wz size); C8 (wz actx)].
    Hypothesis UW' : rw_cells asegs m' U [C8 (wz idv)].
    Hypothesis TST' : stk asegs m' (TH + 2800) (TH + 3168).
    Hypothesis UNW' : rw_cells asegs m' (TH + 3168) [C1 (b8 0)].
    Hypothesis FLG' : rw_cells asegs m' AIAINIT [C1 (b8 1); C1 (b8 0); C2 (wz 0)].
    Hypothesis IA' : ia_after m'.
    Hypothesis SHF' : u8arr asegs m' (sh U) (repeat (b8 kAsanHeapFreeMagic) (Z.to_nat (nsh size))).
    Hypothesis TQc' : rw_cells asegs m' (TH + OT_TQ) [C8 (wz k); C8 (wz (hd 0 (map qb_addr l))); C8 (wz LA); C8 (wz (qc_bytes tq + size))].
    Hypothesis LB' : rw_cells asegs m' LA [C8 (wz 0); C8 (wz (qb_size lb + size)); C8 (wz (lcount + 1))].
    Hypothesis LCHK' : u64arr asegs m' (LA + 24) (wlist (qb_chunks lb ++ [U + -16])).
    Hypothesis LJ' : stk asegs m' (LA + 32 + 8 * lcount) (LA + kBatchSize).

    Let AG : agree_on P m m'. Proof. apply munch_agree. exact MU. Qed.

    (* [comment removed for export] *)
    Let l0 := removelast l.
    Let LSPLIT : l = l0 ++ [lb]. Proof. unfold l0, lb. apply app_removelast_last. exact (proj1 NN). Qed.
    Let TQL : qc_list tq' = l0 ++ [lb'] /\ qc_bytes tq' = qc_bytes tq + size.
    Proof.
      split; [| reflexivity]. unfold tq', tq_app. cbn [qc_list]. fold l lb. fold LA lcount. unfold lb'.
      rewrite LSPLIT at 1 2. rewrite firstn_removelast. reflexivity.
    Qed.
    Let NNf : need_new tq = false. Proof. exact (need_new_false tq (proj1 NN) (proj2 NN)). Qed.
    Let WQ' : WFQ (free_st' s ch tq' (as_cache st)) [] [].
    Proof.
      assert (W0 : WF (set_internal_init st)) by (eapply WF_ext; [ .. | exact WFs]; reflexivity).
      exact (WFQ_free_app (set_internal_init st) ch W0 CHIN ALLOC NNf).
    Qed.
    Let WF' : WF (free_st' s ch tq' (as_cache st)).
    Proof.
      assert (W0 : WF (set_internal_init st)) by (eapply WF_ext; [ .. | exact WFs]; reflexivity).
      pose proof QSZ as [Q1 _]. pose proof PURE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & QC & _).
      exact (WF_free_app (set_internal_init st) ch W0 CHIN ALLOC NNf ltac:(change (as_qcache (set_internal_init st)) with (as_qcache st); rewrite QC; exact NOD)).
    Qed.
    Let OK' : ast_ok s'. Proof. exact (conj (proj1 (proj1 R)) WF'). Qed.

    (* [comment removed for export] *)
    Let NLA : forall b, In b (l0 ++ qc_list (as_gq st)) -> qb_addr b <> LA.
    Proof.
      intros b Hb E. pose proof (batch_addrs_nodup s OK) as ND. fold st in ND. fold tq in ND. fold l in ND. rewrite LSPLIT, <- app_assoc, map_app in ND.
      apply in_app_iff in Hb. destruct Hb as [Hb|Hb].
      - eapply (NoDup_app_disjoint _ _ (qb_addr b) ND); [apply in_map_iff; exists b; auto|]. cbn [map app]. left. fold LA. symmetry. exact E.
      - apply NoDup_app_r in ND. cbn [map app] in ND. apply NoDup_cons_iff in ND. destruct ND as [NI _]. apply NI. fold LA. rewrite <- E. apply in_map_iff. exists b; auto.
    Qed.
    Let INl0 : forall b, In b l0 -> In b (qc_list (as_tq st) ++ qc_list (as_gq st)).
    Proof. intros b Hb. apply in_app_iff. left. fold tq. fold l. rewrite LSPLIT. apply in_app_iff. left. exact Hb. Qed.

    Lemma thread_after_app : thread_rep s' m'.
    Proof.
      destruct (free_cells s m ch R CHIN ALLOC UHI) as (b1o & actxo & q0 & q1 & q2 & q3 & _ & _ & _ & _ & _ & _ & _ & QST & _).
      pose proof TQL as [E1 E2].
      apply (thread_after s ch m m' P tq' (as_cache st) (a_L s) (a_S s) (a_AL s) R CHIN UHI AG WM TST' UNW').
      - apply (junk_of_rw_cells m' _ [C8 q0; C8 q1; C8 q2; C8 q3]); [| reflexivity].
        eapply (rw_cells_transport_pt P m m' AG WM); [exact QST|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add].
        intros a Ha. apply Z_thr3. unfold OT_CACHE. clear - Ha. tlia.
      - rewrite E1, E2. rewrite (map_qb_addr_snoc l0 lb lb' eq_refl). rewrite <- LSPLIT.
        change (last (map qb_addr l) 0) with (last (map qb_addr l) (qb_addr (mkQB 0 0 0 []))). rewrite last_map.
        replace (zlen (l0 ++ [lb'])) with k by (unfold k; rewrite LSPLIT; unfold zlen; rewrite !length_app; reflexivity). exact TQc'.
      - exact Z_thr1.
      - exact Z_thr2.
      - intros a Ha; apply Z_ctx; clear - Ha; tlia.
      - intros a Ha; apply Z_ctx; clear - Ha; tlia.
    Qed.

    Lemma batches_after_app : batches_rep m' (qc_list tq') /\ batches_rep m' (qc_list (as_gq st)).
    Proof.
      pose proof TQL as [E1 _]. rewrite E1. pose proof R as RR. destruct RR as (_ & _ & _ & _ & _ & _ & _ & _ & BT & BG). fold st tq l in BT. fold st in BG.
      split.
      - rewrite LSPLIT in BT.
        assert (GEN : forall r, (forall b, In b r -> In b l0) -> batches_rep m (r ++ [lb]) -> batches_rep m' (r ++ [lb'])).
        { induction r as [|x r IH]; intros SUB BR.
          - cbn [batches_rep app map hd] in BR |- *. split; [| exact I]. destruct BR as [BR _].
            (* [comment removed for export] *)
            pose proof LAST as (_ & _ & _ & INlb & CNT & CNB & _).
            unfold batch_rep in BR |- *. unfold lb'. cbn [qb_addr qb_size qb_count qb_chunks]. destruct BR as (_ & _ & _ & PZ).
            split; [exact LB'|].
            split. { rewrite wlist_app. cbn [wlist map]. unfold ch_chunk_beg, kChunkHeaderSize. fold U. replace (U - 16) with (U + -16) by tlia.
                     rewrite wlist_app in LCHK'. exact LCHK'. }
            split. { intros _. replace (LA + 24 + 8 * (lcount + 1)) with (LA + 32 + 8 * lcount) by tlia.
                     replace (LA + 32 + 8 * lcount + (kBatchSize - 24 - 8 * (lcount + 1))) with (LA + kBatchSize) by tlia. exact LJ'. }
            eapply (poisoned_transport_pt P m m' AG WM); [exact PZ|]. change (Z.of_nat (Z.to_nat (kBatchSize / 8))) with (kBatchSize / 8).
            intros a Ha. exact (Z_batch_sh lb a INlb Ha).
          - cbn [batches_rep app] in BR |- *. destruct BR as [BX BR]. split.
            + rewrite (map_qb_addr_snoc r lb lb' eq_refl).
              apply (batch_after s m m' P R AG WM x _ (INl0 x (SUB x (or_introl eq_refl))) BX).
              * intros a Ha. apply (Z_batch x a (INl0 x (SUB x (or_introl eq_refl)))); [| exact Ha]. apply NLA. apply in_app_iff. left. apply SUB. left. reflexivity.
              * intros a Ha. exact (Z_batch_sh x a (INl0 x (SUB x (or_introl eq_refl))) Ha).
            + apply IH; [intros b Hb; apply SUB; right; exact Hb| exact BR]. }
        apply GEN; [intros b Hb; exact Hb| exact BT].
      - apply (batches_after_list s m m' P R AG WM (qc_list (as_gq st))); [intros b Hb; apply in_app_iff; right; exact Hb| exact BG| |].
        + intros b a Hb Ha. apply (Z_batch b a ltac:(apply in_app_iff; right; exact Hb)); [| exact Ha]. apply NLA. apply in_app_iff. right. exact Hb.
        + intros b a Hb Ha. exact (Z_batch_sh b a ltac:(apply in_app_iff; right; exact Hb) Ha).
    Qed.

    Lemma regions_after_app : forall c0, 0 <= c0 < kNumClasses ->
      region_rep s' m' c0 /\ pclass_rep s' m' c0 /\ region_shadow_rep s' m' c0 /\ region_junk_rep s' m' c0.
    Proof.
      intros c0 Hc0. split; [| split; [| split]].
      - apply (region_after s ch m m' P tq' (as_cache st) (a_L s) (a_S s) (a_AL s) R [] [] WQ' AG WM c0 Hc0 Z_rinfo (fun a Ha => Z_farray c0 a Hc0 Ha) (fun a Ha => Z_tail c0 a Hc0 Ha)).
      - apply (pclass_after s ch m m' P tq' (as_cache st) (a_L s) (a_S s) (a_AL s) R AG WM c0 Hc0 eq_refl).
        intros a Ha. apply Z_thr3. unfold a_cache, OT_CACHE, PCLASS_SIZE, kNumClasses in *. fold TH in Ha. clear - Ha Hc0. tlia.
      - apply (region_shadow_after s ch m m' P tq' (as_cache st) (a_L s) (a_S s) (a_AL s) R [] [] WQ' AG WM c0 Hc0 (fun cp H => H)
                 (fun cp a Hin Ha => Z_freech_sh c0 cp a Hc0 Hin Ha) (fun a Ha => Z_tail_sh c0 a Hc0 Ha) (fun a Ha => Z_farray_sh c0 a Hc0 Ha)).
      - apply (region_junk_after s ch m m' P tq' (as_cache st) (a_L s) (a_S s) (a_AL s) R AG WM c0 Hc0 (fun cp H => H)
                 (fun cp a Hin Ha => Z_freech c0 cp a Hc0 Hin Ha)).
    Qed.

    Lemma armem_after_app : ARmem s' m'.
    Proof.
      destruct batches_after_app as [BT' BG'].
      split. { apply (inst_after s ch m m' P tq' (as_cache st) (a_L s) (a_S s) (a_AL s) R AG WM).
               intros a Ha. apply Z_static; [unfold astatic; left; exact Ha| |]; unfold AINST, OI_MISMATCH, AIAINIT, AIAINST in *; clear - Ha; tlia. }
      split; [exact (flags_after s ch m m' P tq' (as_cache st) (a_L s) (a_S s) (a_AL s) R AG WM FLG' Z_flags)|].
      split; [exact thread_after_app|].
      split; [exact (sec_after s ch m m' P tq' (as_cache st) (a_L s) (a_S s) (a_AL s) R [] [] WQ' AG WM Z_pa Z_sechdr)|].
      split; [unfold ia_rep; change (as_internal_init (a_st s')) with true; exact IA'|].
      split; [exact regions_after_app|].
      split; [exact (chunks_after s ch m m' P tq' (as_cache st) (a_L s) (a_S s) (a_AL s) b1 actx idv bs R CHIN ALLOC UHI AG WM B1 HDR' UW' SHF' BLK
                       Z_rec_self Z_rec_self_sh Z_rec_other Z_rec_other_sh)|].
      exact (conj BT' BG').
    Qed.
    Lemma arepq_after_app : AREPQ s' [] [] m'.
    Proof. split; [exact (proj1 (proj1 R))|]. split; [exact WQ'| exact armem_after_app]. Qed.
    Lemma arep_after_app : AREP s' m'.
    Proof. apply (proj2 (AREP_split s' m')). split; [exact OK'| exact armem_after_app]. Qed.

    Lemma arheap_after_app : ARHEAP s' (lb_remove U LB) m'.
    Proof.
      destruct HR as (_ & ND & LBs).
      split; [exact arep_after_app|]. split; [apply lb_remove_nodup; exact ND|].
      intros b. rewrite lb_remove_In, LBs. unfold alb. change (a_st s') with (free_st' s ch tq' (as_cache st)). rewrite !in_map_iff. split.
      - intros ((x & E & Hx) & NEU). apply filter_In in Hx. destruct Hx as [Hx AX]. exists x. split; [exact E|]. apply filter_In. split; [| exact AX].
        apply (free_old_in s ch m tq' (as_cache st) R CHIN x Hx). intros ->. apply NEU. rewrite <- E. reflexivity.
      - intros (x & E & Hx). apply filter_In in Hx. destruct Hx as [Hx AX]. apply (free_cl s ch m tq' (as_cache st) R CHIN) in Hx.
        destruct Hx as [->|[Hx NEU]]; [cbn in AX; discriminate AX|].
        split; [exists x; split; [exact E| apply filter_In; split; [exact Hx| exact AX]]|]. rewrite <- E. cbn [fst]. exact NEU.
    Qed.
  End Post.

  (* [comment removed for export] *)
  Lemma free_app_model : exists st'' ev, am_free_full st U = Some (st'', ev) /\ same_but_shadow st'' (a_st s') /\ syscalls_of ev = [].
  Proof.
    pose proof BND as B. pose proof PURE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & QM & _ & QC & _).
    assert (NNf : need_new tq = false) by exact (need_new_false tq (proj1 NN) (proj2 NN)).
    assert (IM : forall a, U - 16 <= a -> a + 1 <= U + round_up size 8 -> addr_is_in_mem a = true).
    { intros a Ha Hb. apply (aim_of_aapp _ _ a UHI); clear - Ha Hb; zlets; tlia. }   (* [comment removed for export] *)
    destruct (am_free_app st ch (free_find st ch WFs CHIN) ALLOC ltac:(rewrite QM, QC; unfold kMaxCacheSize; clear - QSZ; tlia)
                ltac:(change 7 with (Z.ones 3); rewrite Z.land_ones by (clear; tlia); clear - B; Z.div_mod_to_equations; tlia)
                ltac:(apply IM; clear - B; zlets; unfold AHI_LO; tlia)
                ltac:(apply IM; clear - B; zlets; unfold AHI_LO; tlia) NNf ltac:(rewrite QC; exact NOD)) as (st'' & ev & E & SBS & SC).
    exists st'', ev. split; [exact E|]. split; [exact SBS| exact SC].
  Qed.

  (* [comment removed for export] *)
  Definition free_app_post : machine_state -> Prop := fun ms' =>
    exists m', free_ret_post sp ra s0 s1 s2 s3 s4 s5 gp tp s6 s7 s8 s9 s10 s11 F fc lo m' ms'
      /\ munch W m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ ARHEAP s' (lb_remove U LB) m' /\ DEPOT asegs d' m'.

  Theorem free_arep_app :
    evt asegs free_app_post
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1bf184) fc None m (seg_rom asegs)).
  Proof.
    pose proof BND as B.
    destruct (free_cells s m ch R CHIN ALLOC UHI) as (b1 & actx & q0 & q1 & q2 & q3 & HDR & Hb1 & ACR & TST & UNW & QC & TQ & QST & INST & IEN).
    pose proof LAST as (LBc & LCHK & LJ & INlb & CNT & CNB & K1 & LA1 & LA2 & LA16 & LAT & LAU & LAD1 & LAD2 & _ & _ & LSZ & QR & HD0).
    fold st tq l lb LA lcount TH U size in LBc, LCHK, LJ, CNT, CNB, LA1, LA2, LA16, LAT, LAU, LAD1, LAD2, LSZ, QR, HD0, TQ.
    pose proof PURE as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & X1 & X2 & X3 & X4 & X5 & V1 & V2 & Q1 & Q2 & Q3 & K0 & K2 & K3 & K4).
    pose proof (free_plu s m ch d R CHIN DPL) as PLU.
    pose proof DPL as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
    pose proof SHB as [[_ [_ SHu]] SBS].
    (* [comment removed for export] *)
    assert (UB : exists ub, rw_cells asegs m U [CB 8 ub]).
    { pose proof R as RR. destruct RR as (_ & _ & _ & _ & _ & _ & _ & CHR & _). pose proof (CHR ch CHIN) as (_ & _ & STI & JR & _).
      rewrite ALLOC in STI. fold U size in JR. pose proof EXT as (_ & _ & E3 & _ & E5 & _).
      pose proof (stk_of_rw_cells asegs _ _ _ BLK) as SK. cbn [cells_size csize Nat.add] in SK.
      replace (U + Z.of_nat (Z.to_nat size + 0)) with (U + size) in SK by (clear - B; tlia).
      destruct (Z.le_gt_cases 8 size) as [LE|GT].
      - destruct (stk_split asegs _ _ (U + 8) _ SK ltac:(clear - LE; tlia)) as [SK1 _]. destruct (stk_cells _ _ _ SK1 ltac:(clear - LE; tlia)) as [ub Hub].
        exists ub. replace (Z.to_nat (U + 8 - U)) with 8%nat in Hub by (clear - LE; tlia). exact Hub.
      - pose proof (junk_stk' _ _ _ JR ltac:(clear - B; tlia) ltac:(clear - B E5; acb; tlia) ltac:(clear - GT E3; tlia)) as SJ.
        replace (U + size + (ch_end ch - (U + size))) with (ch_end ch) in SJ by (clear - GT; tlia).
        destruct (stk_split asegs _ _ (U + 8) _ SJ ltac:(clear - GT E3 B; tlia)) as [SJ1 _].
        pose proof (stk_merge asegs _ _ _ _ SK SJ1 ltac:(clear - GT B; tlia)) as SK8.
        destruct (stk_cells _ _ _ SK8 ltac:(clear - GT; tlia)) as [ub Hub]. exists ub. replace (Z.to_nat (U + 8 - U)) with 8%nat in Hub by (clear - GT; tlia). exact Hub. }
    destruct UB as [ub UB].
    eapply evt_mono.
    { eapply (@free_append _ ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo d (as_internal_init st)
                ATSD CTX TH (a_top s) (a_bot s) CH sb U size b1 actx ub kQuarantineMaxSize kQuarantineMinSize kMaxCacheSize sbs
                k (hd 0 (map qb_addr l)) LA (qc_bytes tq)) with (lsize := qb_size lb) (lcount := lcount) (lchunks := qb_chunks lb).
      - exact LO.
      - exact HI.
      - constructor. exact SPA.
      - constructor. exact SPT.
      - constructor. rewrite TP. unfold wz, ATP, AIMG_TOP. rewrite unsigned_lit by (clear; tlia). clear; tlia.
      - constructor. unfold ATSD, AIMG_TOP. pose proof PL as (_ & _ & _ & _ & _ & _ & pT1 & pT2 & pT3 & _ & pX2 & pX3 & _). fold TH in pT1, pT2, pT3. fold CTX in pX2, pX3.
        unfold kPageSize in pT1, pT2, pT3. split; [clear; tlia|]. split; [clear; tlia|]. split; [exact pX2|]. split; [exact pX3|]. split; [exact pT2|]. split; [exact pT3|].
        clear - pT1. Z.div_mod_to_equations. tlia.
      - constructor. unfold kSpaceSize. clear - X4 X5 Y6. zlets. unfold kSpaceSize in *. tlia.
      - constructor. unfold disj, kSpaceSize, kPageSize in G1, G2, G3, G4, G5, G6. fold TH in G1, G2. fold sb in G3, G4. fold CTX in G5, G6.
        pose proof DPL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & dN1 & _ & dN3 & _).   (* [comment removed for export] *)
        repeat match goal with |- _ /\ _ => split end; try exact dN1; try exact dN3; clear - G1 G2 G3 G4 G5 G6 B; zlets; unfold kSpaceSize; tlia.
      - constructor. exact PLU.
      - constructor. clear - V1 V2. zlets. unfold kPageSize in V1. tlia.
      - exact DLO.
      - exact DCAP.
      - exact FCH.
      - exact Ha0.
      - constructor. clear - Z1 Z2 Z3 Z4 Z5 Z6. zlets. destruct Z2 as (_ & ZU & ZT). repeat match goal with |- _ /\ _ => split end; [apply (aapp_sub _ _ _ _ ZU); tlia| tlia..].   (* [comment removed for export] *)
      - clear - Z1 QSZ. zlets. tlia.
      - exact Hb1.
      - exact ACR.
      - clear - QSZ. zlets. unfold kMaxCacheSize, kQuarantineMaxSize, kQuarantineMinSize in *. tlia.
      - exact SBS.
      - pose proof (batches_len_bound s m R) as BL. clear - K3 BL. zlets. unfold zlen in *. rewrite length_app in BL. tlia.
      - exact K4.
      - rewrite TP. exact IEN.
      - exact MI.
      - exact ST.
      - exact UNW.
      - exact FLG4.
      - exact IAX.
      - exact DEP.
      - exact HDR.
      - exact UB.
      - exact TST.
      - exact QC.
      - exact SHu.
      - exact TQ.
      - exact K1.
      - constructor. clear - LA1 LA2 LA16 LAT. zlets. unfold kBatchSize, AHI_LO in *. repeat split; tlia.
      - constructor. unfold kBatchSize. exact (conj LAU (conj LAD1 LAD2)).
      - clear - CNT CNB NN. zlets. unfold kBatchCount in *. zlets. tlia.
      - exact NOD.
      - exact LBc.
      - exact LCHK.
      - unfold kBatchSize. replace (LA + 8192) with (LA + kBatchSize) by reflexivity. exact LJ. }
    intros ms' PO.
    destruct PO as (m' & RET & FC & TQ4 & LB4 & LCHK4 & LJ4).
    destruct FC as (MU & WM & MI' & ST' & HDR' & UW' & TST' & UNW' & FLG' & IA' & DEP' & SHF' & _ & _).
    exists m'. split; [exact RET|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|].
    split; [| exact DEP'].
    eapply (arheap_after_app m' b1 actx MU WM Hb1 HDR' UW' TST' UNW' FLG' IA' SHF' TQ4 LB4 LCHK4).
    unfold kBatchSize. exact LJ4.
  Qed.
End FreeApp.
