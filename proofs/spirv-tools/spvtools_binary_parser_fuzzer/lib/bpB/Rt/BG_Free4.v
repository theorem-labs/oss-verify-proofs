(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BW_0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FMapPositive.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BImage BZBridge BSysStep BSFModel BellsX BArr BacX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BothAllocModel.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BllocWf BllocKit BllocRep BllocRepFacts BllocRepFacts2 BsDepotInv BW_MallocBase BW_IAInit BW_Enqueue2 BS_Free1 BllocWalkKit BG_MallocModel BG_WFHit BG_Malloc BG_Malloc2 BG_FreeModel BG_WFFree BG_Free1 BG_FreeFacts BG_Free2 BG_Free3 BG_RepQ BG_RepQFacts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BerfLia.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Ltac lia ::=
  first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].

Section HCW.
  Context {HCEIL : HeapCeil}.

Lemma hd_map_app_single : forall (r : list qbatch) (x : Z), hd 0 (map qb_addr r ++ [x]) = if zlen r =? 0 then x else hd 0 (map qb_addr r).
Proof. intros r x. destruct r as [|b r]; [reflexivity|]. rewrite zlen_cons. cbn [map app hd]. destruct (zlen r + 1 =? 0) eqn:E; [| reflexivity]. apply Z.eqb_eq in E. unfold zlen in E. tlia. Qed.
Lemma hd_map_app_cons : forall (r : list qbatch) (b : qbatch) (t1 t2 : list qbatch), hd 0 (map qb_addr (r ++ b :: t1)) = hd 0 (map qb_addr (r ++ b :: t2)).
Proof. intros r b t1 t2. destruct r; reflexivity. Qed.
Lemma u64arr_nil' : forall m A, 0 <= A -> A <= 2^64 -> u64arr asegs m A [].
Proof.
  intros m A H0 H1. unfold u64arr. cbn [u64s length map concat Z.of_nat Z.mul]. unfold bytes_at, wr_at. cbn [length Z.of_nat].
  change (8 * 0) with 0. rewrite Z.add_0_r. repeat split; tlia.
Qed.
Lemma u64arr_one : forall m A w, rw_cells asegs m A [C8 w] -> u64arr asegs m A [w].
Proof.
  intros m A w H. pose proof (proj2 H) as (A0 & A1 & _). cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat] in A1.
  apply (proj2 (u64arr_snoc asegs m A [] w)). split; [apply u64arr_nil'; [exact A0| tlia]| cbn [length Z.of_nat]; rewrite Z.mul_0_r, Z.add_0_r; exact H].
Qed.

Section FreeNewPost.
  Variables (s : ast) (m m' : mem) (d : depot) (lo spv : Z) (ch : chunk) (bs : list byte) (cp : Z) (rest : list Z).
  Variables (L' S' : list (word * word)) (AL' : Z) (b1 actx idv : Z) (j0 j1 j2 j3 : word).

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
  Let cnt := pc_count (get_pc st kBatchClass).
  Let B := compact_to_addr st kBatchClass cp.

  Let nb := mkQB B (size + kBatchSize) 1 [ch_chunk_beg ch].
  Let tq' := tq_new tq B (ch_chunk_beg ch) size.
  Let cache' := upd_nth (as_cache st) (zidx kBatchClass) (mkPC (cnt - 1) rest).
  Let s' := free_s' s ch tq' cache' L' S' AL'.

  Let Wh : list ivl := free_head_W lo spv TH U size d.
  Let Wn : list ivl := enq_new_W lo spv TH B LA.
  Let W : list ivl := Wh ++ Wn.
  Let P := outside W.

  Hypothesis R : AREP s m.
  Hypothesis CHIN : In ch (chunk_list st).
  Hypothesis ALLOC : ch_state ch = CAllocated.
  Hypothesis UHI : aapp (ch_user_beg ch - 16) (16 + round_up (ch_used ch) 8).
  Hypothesis DPL : depot_placed s d.
  Hypothesis LO : aceil <= lo.
  Hypothesis DLO : d_nb d + 16 * 65536 <= lo /\ d_sb d + 8 * 32768 <= lo.
  Hypothesis PCS : pc_chunks (get_pc st kBatchClass) = cp :: rest.
  Hypothesis NN : need_new tq = true.
  Hypothesis NOD : qc_bytes tq + size + kBatchSize <= kMaxCacheSize.
  Hypothesis QSZ : size <= kQuarantineMaxSize /\ size < 2^32.
  Hypothesis BLK : rw_cells asegs m U [CB (Z.to_nat size) bs].
  Hypothesis AG : agree_on P m m'.
  Hypothesis WM : wmono asegs m m'.

  Hypothesis B1 : 0 <= b1 < 256 /\ b1 mod 128 = 17.
  Hypothesis HDR' : rw_cells asegs m' (U + -16) [C1 (b8 3); C1 (b8 b1); C2 (wz 0); C4 (wz size); C8 (wz actx)].
  Hypothesis UW' : rw_cells asegs m' U [C8 (wz idv)].
  Hypothesis TST' : stk asegs m' (TH + 2800) (TH + 3168).
  Hypothesis UNW' : rw_cells asegs m' (TH + 3168) [C1 (b8 0)].
  Hypothesis FLG' : rw_cells asegs m' AIAINIT [C1 (b8 1); C1 (b8 0); C2 (wz 0)].
  Hypothesis IA' : ia_after m'.
  Hypothesis SHF' : u8arr asegs m' (sh U) (repeat (b8 kAsanHeapFreeMagic) (Z.to_nat (nsh size))).
  Hypothesis TQc' : rw_cells asegs m' (TH + OT_TQ)
      [C8 (wz (k + 1)); C8 (wz (if k =? 0 then B else hd 0 (map qb_addr l))); C8 (wz B); C8 (wz (qc_bytes tq + (size + kBatchSize)))].
  Hypothesis LAn' : k <> 0 -> rw_cells asegs m' LA [C8 (wz B)].
  Hypothesis NB' : rw_cells asegs m' B [C8 (wz 0); C8 (wz (size + kBatchSize)); C8 (wz 1); C8 (wz (U + -16))].
  Hypothesis NBJ' : stk asegs m' (B + 32) (B + kBatchSize).
  Hypothesis PC1' : rw_cells asegs m' (TH + 2128) [C4 (wz (cnt - 1))].
  Hypothesis PC3' : u32arr asegs m' (TH + 2144) (wlist (rev rest)).
  Hypothesis PC4' : stk asegs m' (TH + 2144 + 4 * (cnt - 1)) (TH + 2208).
  Hypothesis STATS' : rw_cells asegs m' (TH + 2768) [C8 j0; C8 j1; C8 j2; C8 j3].

  Ltac wsplit := unfold W, Wh, Wn, free_head_W, enq_new_W; cbn [outside depot_W app]; repeat split; try exact I.
  Ltac zlets := repeat match goal with H := _ |- _ => subst H end.
  Ltac zfin := zlets; unfold AHI_LO, AIMG_TOP, ALOWSH_LO, OT_TQ, OT_CACHE, a_ri, a_sb, disj, kPageSize, kBatchSize, kSpaceSize, kPtrArrayReserve in *; tlia.

  Let OK : ast_ok s. Proof. exact (proj1 R). Qed.
  Let PL : placed_ok s. Proof. exact (proj1 OK). Qed.
  Let WFs : WF st. Proof. exact (proj2 OK). Qed.
  Let PURE := free_pure s m ch R CHIN UHI.
  Let EXT : ch_lo ch <= U - 16 /\ U + round_up size 8 <= ch_end ch /\ U + 8 <= ch_end ch /\ 7241728 <= ch_lo ch /\ ch_end ch <= aceil
            /\ ch_lo ch mod 8 = 0 /\ ch_end ch mod 8 = 0 /\ ch_alloc_beg ch + ch_rz ch = U /\ 16 <= ch_rz ch /\ ch_lo ch <= ch_alloc_beg ch.
  Proof.
    pose proof (record_ext s OK ch CHIN) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9).
    pose proof (chunk_geom s OK ch CHIN) as (G1 & G2 & G3 & G4 & G5 & G6 & _).
    pose proof (record_band s OK ch CHIN) as RB. unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AIMG_TOP, AHI_LO in RB. unfold AHI_LO in UHI.
    clear - X1 X2 X3 X4 X5 X6 X7 X8 X9 G1 G2 G3 G4 G5 G6 RB UHI. subst U size. pose proof (aapp_env _ _ UHI ltac:(clear - G3 G5; tlia)) as [UE _]. unfold AHI_LO, AIMG_TOP in *. repeat split; try assumption; tlia.
  Qed.

  Let HC24 : 0 <= kBatchClass < kNumClasses. Proof. unfold kBatchClass, kNumClasses. tlia. Qed.
  Let CPIN : In cp (pc_chunks (get_pc st kBatchClass)). Proof. rewrite PCS. left. reflexivity. Qed.
  Let CVB : carved st kBatchClass B. Proof. exact (carved_cache st kBatchClass cp WFs HC24 CPIN). Qed.
  Let BR : sb + kBatchClass * 2^32 <= B /\ B + kBatchSize <= sb + kBatchClass * 2^32 + kFreeArrayOffset /\ B + kBatchSize <= aceil /\ B mod 16 = 0
           /\ B = sb + kBatchClass * 2^32 + cp * 16 /\ 0 <= cp < 2^32.
  Proof.
    pose proof (carved_range st _ _ WFs CVB) as (C1 & C2 & _). pose proof (carved_in_space s OK _ _ CVB) as (S1 & S2 & _).
    destruct CVB as (_ & _ & C3 & C4 & _). pose proof PL as (SB1 & _ & SB3 & _).
    rewrite region_beg_eq in C1, C2, C3, C4. change (class_size kBatchClass) with 8192 in *.
    assert (EB : B = sb + kBatchClass * 2^32 + cp * 16) by (unfold B, sb, a_sb; rewrite compact_to_addr_eq, region_beg_eq; reflexivity).
    clear - C1 C2 C3 C4 S1 S2 SB1 SB3 EB. subst B sb st. unfold a_sb, kBatchSize, kBatchClass, kFreeArrayOffset, kSpaceSize, kPageSize in *.
    repeat split; try tlia; Z.div_mod_to_equations; tlia.
  Qed.
  Let CNT : cnt = zlen rest + 1 /\ 1 <= cnt <= 16.
  Proof.
    pose proof (WF_cache st kBatchClass WFs HC24) as CO. pose proof (co_count _ _ CO) as C1. pose proof (co_bound _ _ CO) as C2.
    unfold cnt. rewrite C1, PCS, zlen_cons. rewrite C1, PCS, zlen_cons in C2. change (max_count kBatchClass) with 2 in *.
    assert (0 <= zlen rest) by (unfold zlen; tlia). destruct (as_cache_inited st); tlia.
  Qed.

  Let LAF : (l = [] /\ LA = 0 /\ k = 0)
            \/ (l <> [] /\ 1 <= k /\ AHI_LO <= LA /\ LA + kBatchSize <= aceil /\ (TH + 4096 <= LA \/ LA + kBatchSize <= TH)
                /\ (LA + kBatchSize <= U - 16 \/ U + 8 <= LA)
                /\ (d_nb d + 16 * 65536 <= LA \/ LA + kBatchSize <= d_nb d) /\ (d_sb d + 8 * 32768 <= LA \/ LA + kBatchSize <= d_sb d)
                /\ sb + kBatchClass * 2^32 <= LA /\ LA + kBatchSize <= sb + kBatchClass * 2^32 + kFreeArrayOffset
                /\ (B + kBatchSize <= LA \/ LA + kBatchSize <= B) /\ In lb (qc_list (as_tq st) ++ qc_list (as_gq st))).
  Proof.
    assert (D : l = [] \/ l <> []) by (destruct l; [left; reflexivity| right; discriminate]).
    destruct D as [EL|NE].
    - left. split; [exact EL|]. unfold LA, lb, k. rewrite EL. split; reflexivity.
    - right.
      pose proof (free_last_cells s m ch d R CHIN DPL NE) as (_ & _ & _ & INlb & _ & _ & K1 & LA1 & LA2 & _ & LAT & LAU & LAD1 & LAD2 & LR1 & LR2 & _).
      pose proof (carved_vs_batch s OK _ _ CVB lb INlb ltac:(hci; apply (batch_not_free s OK lb kBatchClass cp INlb HC24 (or_intror CPIN)))) as BL.
      change (class_size kBatchClass) with kBatchSize in BL.
      split; [exact NE|]. fold st tq l k lb LA in K1, LA1, LA2, LAT, LAU, LAD1, LAD2, LR1, LR2, BL, INlb |- *. fold TH U sb in LAT, LAU, LR1, LR2.
      repeat match goal with |- _ /\ _ => split end; try assumption. clear - BL. tlia.
  Qed.

  Let BND : aceil <= lo /\ 4096 <= TH /\ TH + 4096 <= aceil /\ 7241728 <= CTX /\ CTX + 160 <= aceil
            /\ 0x10007fff8000 <= sb /\ sb + 137438953472 + 4096 <= aceil /\ 7241728 <= a_pa s /\ a_pa s + 8388608 <= aceil
            /\ 7241728 <= d_nb d /\ d_nb d + 16 * 65536 <= aceil /\ 7241728 <= d_sb d /\ d_sb d + 8 * 32768 <= aceil
            /\ 7241744 <= U /\ U + round_up size 8 <= aceil /\ 1 <= size /\ size <= round_up size 8 /\ round_up size 8 = 8 * nsh size
            /\ 0x10007fff8000 <= B /\ B + 8192 <= aceil
            /\ 2148356096 <= sh U /\ sh U + nsh size <= 0x10007fff8000 /\ U mod 16 = 0 /\ 1 <= cnt <= 16 /\ 0 <= LA.
  Proof.
    pose proof PURE as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & X1 & X2 & X3 & _).
    pose proof PL as (_ & _ & _ & P1 & P2 & P3 & _). pose proof DPL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & N1 & N2 & N3 & N4).
    pose proof BR as (B1' & B2' & B3' & _). pose proof CNT as [_ CN]. pose proof EXT as (E1 & _ & E3 & _).
    apply aapp_env in P2; [| unfold kPtrArrayReserve; clear; tlia]. apply aapp_env in N1; [| clear; tlia]. apply aapp_env in N3; [| clear; tlia].
    assert (LA0 : 0 <= LA) by (destruct LAF as [(_ & LA0 & _)|(_ & _ & L1 & _)]; [rewrite LA0; apply Z.le_refl| clear - L1; unfold AHI_LO in L1; tlia]).
    change (class_size kBatchClass) with 8192 in *.
    clear - Z1 Z2 Z3 Z4 Z5 Z6 Y1 Y2 Y4 Y5 X1 X2 P2 P3 N1 N2 N3 N4 LO B1' B2' B3' CN E1 E3 LA0.
    zlets. unfold AHI_LO, AIMG_TOP, kSpaceSize, kPageSize, kPtrArrayReserve, kBatchSize, kBatchClass, kFreeArrayOffset in *.
    destruct Z2 as (ZA & _ & ZB). unfold aapp, aapp_lo, aapp_hi, AIMG_TOP, ALOWSH_LO, AHI_LO in ZA, ZB.
    assert (SH : 2148356096 <= sh (ch_user_beg ch) /\ sh (ch_user_beg ch) + nsh (ch_used ch) <= 0x10007fff8000).
    { acb. clear - ZA Z3 Z6 Z1 ACEILB. unfold sh, ASHADOW_BASE. Z.div_mod_to_equations. tlia. }
    clear ZA. repeat match goal with |- _ /\ _ => split end; try tlia.
  Qed.
  Let LAlo : LA = 0 \/ 0x10007fff8000 <= LA.
  Proof. destruct LAF as [(_ & LA0 & _)|(_ & _ & L1 & _)]; [left; exact LA0| right; clear - L1; unfold AHI_LO in L1; tlia]. Qed.

  Let BDJ : (TH + 4096 <= B \/ B + 8192 <= TH) /\ (B + 8192 <= ch_lo ch \/ ch_end ch <= B)
            /\ (d_nb d + 16 * 65536 <= B \/ B + 8192 <= d_nb d) /\ (d_sb d + 8 * 32768 <= B \/ B + 8192 <= d_sb d).
  Proof.
    pose proof (carved_vs_thread s OK _ _ CVB) as BT. pose proof (carved_vs_depot s OK _ _ CVB d DPL) as [BD1 BD2].
    pose proof (freech_vs_record s OK ch CHIN kBatchClass cp HC24 (or_intror CPIN)) as BU.
    change (class_size kBatchClass) with 8192 in *. clear - BT BD1 BD2 BU. zlets. unfold kPageSize in *. repeat split; tlia.
  Qed.

  Let BANDS : hidden ((TH + 4096 <= 65536 \/ (7241728 <= TH /\ TH + 4096 <= 2147446784) \/ 17594333495296 <= TH)
                   /\ (CTX + 160 <= 2147446784 \/ 17594333495296 <= CTX)
                   /\ (a_pa s + 8388608 <= 2147446784 \/ 17594333495296 <= a_pa s)
                   /\ (d_nb d + 16 * 65536 <= 2147446784 \/ 17594333495296 <= d_nb d)
                   /\ (d_sb d + 8 * 32768 <= 2147446784 \/ 17594333495296 <= d_sb d)).
  Proof.
    pose proof PL as (_ & _ & _ & _ & P2 & _ & _ & T2 & _ & _ & X2 & _). pose proof DPL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & N1 & _ & N3 & _).
    fold TH in T2. fold CTX in X2.
    split. split; [exact (akobj_lit _ _ T2)|]. split; [exact (aapp_lit _ _ X2)|].
    split; [pose proof (aapp_lit _ _ P2) as L; unfold kPtrArrayReserve in L; exact L|].
    split; [exact (aapp_lit _ _ N1)| exact (aapp_lit _ _ N3)].
  Qed.
  Tactic Notation "bands_as" simple_intropattern(p) := (let X := fresh "BX" in pose proof BANDS as X; destruct X as [p]).

  Let UBANDS : hidden ((sh U + nsh size <= U - 16 \/ U + round_up size 8 <= sh U)
                    /\ (U + round_up size 8 <= 2147446784 \/ 17594333495296 <= U - 16)
                    /\ (ch_end ch <= 2147446784 \/ 17594333495296 <= ch_lo ch)).
  Proof.
    pose proof PURE as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & _). pose proof (record_band s OK ch CHIN) as RBB. destruct Z2 as (ZA & _).
    clear - Z1 ZA Z3 Z5 Z6 RBB. constructor. subst U size. unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AIMG_TOP, AHI_LO in ZA, RBB. acb.
    split; [| clear - ZA RBB; tlia]. clear - ZA Z3 Z6 Z1 ACEILB. unfold sh, ASHADOW_BASE. Z.div_mod_to_equations. tlia.
  Qed.
  Tactic Notation "ubands_as" simple_intropattern(p) := (let X := fresh "UBX" in pose proof UBANDS as X; destruct X as [p]).

  Lemma Zn_core : forall a, a < aceil -> ~ (AIAINIT <= a < AIAINIT + 4) -> ~ (AIAINST <= a < AIAINST + 0x81030) ->
    ~ (2567960 <= a < 6762288) -> ~ (2502408 <= a < 2502436) ->
    ~ (U - 16 <= a < U - 12) -> ~ (U <= a < U + 8) -> ~ (TH + 80 <= a < TH + 112) -> ~ (TH + 2128 <= a < TH + 2132) -> ~ (TH + 2784 <= a < TH + 2792) ->
    ~ (TH + 2800 <= a < TH + 3169) -> ~ (sh U <= a < sh U + nsh size) -> ~ (B <= a < B + 32) -> ~ (LA <= a < LA + 8) ->
    ~ (d_nb d <= a < d_nb d + 16 * 65536) -> ~ (d_sb d <= a < d_sb d + 8 * 32768) -> outside W a.
  Proof.
    intros a Ha N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 N12 N13 N14 N15. pose proof BND as BB. clear - Ha N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 N12 N13 N14 N15 BB.
    wsplit; unfold AIAINIT, AIAINST, OT_TQ in *; tlia.
  Qed.

  Lemma Zn_stat : forall a, 65536 <= a < AIMG_TOP -> ~ (AIAINIT <= a < AIAINIT + 4) -> ~ (AIAINST <= a < AIAINST + 0x81030) ->
    ~ (2567960 <= a < 6762288) -> ~ (2502408 <= a < 2502436) -> outside W a.
  Proof.
    intros a Ha N1 N2 N3 N4. pose proof BND as BB. pose proof LAlo as LL. bands_as (BT & _).
    apply Zn_core; try assumption; clear - Ha BB LL BT; unfold AIMG_TOP, AHI_LO in *; acb; try tlia.
    all: unfold sh, ASHADOW_BASE; Z.div_mod_to_equations; tlia.
  Qed.

  Lemma Zn_hi : forall a, (AIMG_TOP <= a < ALOWSH_LO \/ AHI_LO <= a < aceil) -> ~ (U - 16 <= a < U - 12) -> ~ (U <= a < U + 8) -> ~ (TH + 80 <= a < TH + 112) ->
    ~ (TH + 2128 <= a < TH + 2132) -> ~ (TH + 2784 <= a < TH + 2792) -> ~ (TH + 2800 <= a < TH + 3169) ->
    ~ (B <= a < B + 32) -> ~ (LA <= a < LA + 8) -> ~ (d_nb d <= a < d_nb d + 16 * 65536) -> ~ (d_sb d <= a < d_sb d + 8 * 32768) ->
    outside W a.
  Proof.
    intros a Ha N1 N2 N3 N4 N5 N6 N7 N8 N9 N10. pose proof BND as BB.
    apply Zn_core; try assumption; clear - Ha BB; unfold AIAINIT, AIAINST, AIMG_TOP, ALOWSH_LO, AHI_LO in *; acb; tlia.
  Qed.

  Lemma Zn_sh : forall a, ASHADOW_BASE <= a < AHI_LO -> ~ (sh U <= a < sh U + nsh size) -> outside W a.
  Proof.
    intros a Ha N1. pose proof BND as BB. pose proof LAlo as LL. bands_as (BT & _ & _ & BN & BS). ubands_as (_ & UB & _).
    apply Zn_core; try assumption; clear - Ha BB LL BT BN BS UB; unfold AIAINIT, AIAINST, AHI_LO, ASHADOW_BASE in *; acb; tlia.
  Qed.

  Lemma Zn_static : forall a, astatic a -> ~ (AIAINIT <= a < AIAINIT + 4) -> ~ (AIAINST <= a < AIAINST + 0x81030) -> outside W a.
  Proof.
    intros a Ha N1 N2. apply Zn_stat; [| exact N1| exact N2| |]; clear - Ha; unfold astatic in Ha;
    unfold AINST, OI_MISMATCH, AFLAGS, ACFLAGS, ASHBASE_CELL, AHIGHMEMEND, ACANPOISON, AINITED, AALLOCFLAGS, AIAINIT, AHOOKS, AREALMEMSET,
           AIAINST, AGOT_LO, APAGESZ, ASECNAME, APRIMNAME, ATLSSLOT, ATSD, ALSANDIS, AGOT2, AIMG_LO, AIMG_TOP in *; tlia.
  Qed.
  Lemma Zn_flags : forall a, aflags_range a -> ~ (AIAINIT <= a < AIAINIT + 4) -> ~ (AIAINST <= a < AIAINST + 0x81030) -> outside W a.
  Proof.
    intros a Ha N1 N2. apply Zn_stat; [| exact N1| exact N2| |]; clear - Ha; unfold aflags_range in Ha;
    unfold AFLAGS, ACFLAGS, ASHBASE_CELL, AHIGHMEMEND, ACANPOISON, AINITED, ACTXSIZE, ATSDINIT, AALLOCFLAGS, AIAINIT, AHOOKS, ADYING,
           AREALMEMSET, AIAINST, AGOT_LO, APAGESZ, ASECNAME, APRIMNAME, ATLSSLOT, ATSD, ALSANDIS, AGOT2, AIMG_LO, AIMG_TOP in *; tlia.
  Qed.
  Lemma Zn_SH : forall lo' kk a, 0 <= lo' -> lo' mod 8 = 0 -> 0 <= kk -> lo' + 8 * kk <= aceil ->
    (lo' + 8 * kk <= U \/ U + round_up size 8 <= lo') -> sh lo' <= a < sh lo' + kk -> outside W a.
  Proof.
    intros lo' kk a H0 H8 Hk Hhi Hd Ha. pose proof BND as BB.
    assert (U8 : U mod 8 = 0) by (clear - BB; Z.div_mod_to_equations; tlia).
    assert (SS : sh lo' + kk <= sh U \/ sh U + nsh size <= sh lo').
    { apply sh_sep; try assumption; clear - BB Hd; tlia. }
    assert (SB : 0x7fff8000 <= sh lo' /\ sh lo' + kk <= 0x10007fef8000) by (clear - H0 Hk Hhi; acb; unfold sh, ASHADOW_BASE; Z.div_mod_to_equations; tlia).
    apply Zn_sh; [unfold ASHADOW_BASE, AHI_LO| ]; clear - Ha SS SB; tlia.
  Qed.

  Lemma Zn_rec_other : forall x a, In x (chunk_list st) -> x <> ch -> ch_lo x <= a < ch_end x -> outside W a.
  Proof.
    intros x a Hx NE Ha. pose proof BND as BB.
    pose proof (record_ext s OK x Hx) as (X1 & X2 & _). pose proof (record_vs_record s OK ch CHIN x Hx NE) as D. pose proof EXT as (E1 & _ & E3 & _).
    pose proof (rec_vs_thread s m x R Hx) as RT. pose proof (rec_vs_depot s m x d R Hx DPL) as [RD1 RD2].
    pose proof (record_band s OK x Hx) as RBx. unfold aapp, aapp_lo, aapp_hi in RBx.
    pose proof (freech_vs_record s OK x Hx kBatchClass cp HC24 (or_intror CPIN)) as BX. change (class_size kBatchClass) with 8192 in BX.
    assert (LX : ch_end x <= LA \/ LA + 8 <= ch_lo x).
    { destruct LAF as [(_ & LA0 & _)|(NE' & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & INlb)].
      - rewrite LA0. clear - X1. unfold AIMG_TOP in X1. tlia.
      - pose proof (batch_vs_record s OK x Hx lb INlb) as BL. clear - BL. zfin. }
    apply Zn_hi; clear - Ha BB X1 X2 D E1 E3 RT RD1 RD2 BX LX RBx; zfin.
  Qed.
  Lemma Zn_rec_self : forall a, ch_lo ch <= a < ch_end ch -> ~ (U - 16 <= a < U - 12) -> ~ (U <= a < U + 8) -> outside W a.
  Proof.
    intros a Ha N1 N2. pose proof BND as BB. pose proof EXT as (E1 & E2 & E3 & E4 & E5 & _).
    pose proof (rec_vs_thread s m ch R CHIN) as RT. pose proof (rec_vs_depot s m ch d R CHIN DPL) as [RD1 RD2].
    pose proof (freech_vs_record s OK ch CHIN kBatchClass cp HC24 (or_intror CPIN)) as BX. change (class_size kBatchClass) with 8192 in BX.
    assert (LX : ch_end ch <= LA \/ LA + 8 <= ch_lo ch).
    { destruct LAF as [(_ & LA0 & _)|(NE' & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & INlb)].
      - rewrite LA0. clear - E4. unfold AHI_LO in E4. tlia.
      - pose proof (batch_vs_record s OK ch CHIN lb INlb) as BL. clear - BL. zfin. }
    ubands_as (_ & _ & UC). apply Zn_hi; clear - Ha N1 N2 BB E4 E5 RT RD1 RD2 BX LX UC; zfin.
  Qed.
  Lemma Zn_rec_self_sh : forall a, sh (ch_lo ch) <= a < sh (ch_end ch) -> ~ (sh U <= a < sh U + nsh size) -> outside W a.
  Proof.
    intros a Ha N1. pose proof EXT as (_ & _ & _ & E4 & E5 & _). apply Zn_sh; [| exact N1].
    clear - Ha E4 E5. acb. unfold AHI_LO, sh in *. unfold ASHADOW_BASE in *. Z.div_mod_to_equations. tlia.
  Qed.
  Lemma Zn_rec_other_sh : forall x lo' kk a, In x (chunk_list st) -> x <> ch -> ch_lo x <= lo' -> lo' + 8 * kk <= ch_end x -> lo' mod 8 = 0 -> 0 <= kk ->
    sh lo' <= a < sh lo' + kk -> outside W a.
  Proof.
    intros x lo' kk a Hx NE G1 G2 G3 G4 Ha. pose proof (record_ext s OK x Hx) as (X1 & X2 & _).
    pose proof (record_vs_record s OK ch CHIN x Hx NE) as D. pose proof EXT as (E1 & E2 & _).
    apply (Zn_SH lo' kk a); try assumption.
    - clear - G1 X1. unfold AIMG_TOP in X1. tlia.
    - clear - G2 X2. tlia.
    - clear - G1 G2 D E1 E2. tlia.
  Qed.

  Lemma Zn_batch : forall b a, In b (qc_list (as_tq st) ++ qc_list (as_gq st)) -> qb_addr b <> LA -> qb_addr b <= a < qb_addr b + kBatchSize -> outside W a.
  Proof.
    intros b a Hb NE Ha. pose proof BND as BB. pose proof (batch_carved s OK b Hb) as (CV & _).
    pose proof (batch_in_space s OK b Hb) as (P1 & P2 & _). pose proof (batch_vs_record s OK ch CHIN b Hb) as D. pose proof EXT as (E1 & _ & E3 & _).
    pose proof (carved_vs_batch s OK _ _ CVB b Hb ltac:(hci; apply (batch_not_free s OK b kBatchClass cp Hb HC24 (or_intror CPIN)))) as BX.
    change (class_size kBatchClass) with 8192 in BX.
    pose proof (carved_vs_thread s OK _ _ CV) as CT. pose proof (carved_vs_depot s OK _ _ CV d DPL) as [CD1 CD2].
    change (class_size kBatchClass) with 8192 in *.
    assert (LX : qb_addr b + 8192 <= LA \/ LA + 8 <= qb_addr b).
    { destruct LAF as [(_ & LA0 & _)|(NE' & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & INlb)].
      - rewrite LA0. clear - P1 BB. zfin.
      - pose proof (batch_carved s OK lb INlb) as (CVl & _). pose proof (carved_vs_batch s OK _ _ CVl b Hb NE) as BL.
        change (class_size kBatchClass) with 8192 in BL. clear - BL. zfin. }
    apply Zn_hi; clear - Ha BB P1 P2 D E1 E3 BX CT CD1 CD2 LX; zfin.
  Qed.

  Lemma Zn_lastbatch : forall a, l <> [] -> LA + 8 <= a < LA + kBatchSize -> outside W a.
  Proof.
    intros a NE Ha. pose proof BND as BB.
    destruct LAF as [(EL & _)|(_ & _ & L1 & L2 & L3 & L4 & L5 & L6 & _ & _ & L9 & _)]; [exfalso; exact (NE EL)|].
    apply Zn_hi; clear - Ha BB L1 L2 L3 L4 L5 L6 L9; zfin.
  Qed.
  Lemma Zn_batch_sh : forall b a, In b (qc_list (as_tq st) ++ qc_list (as_gq st)) -> sh (qb_addr b) <= a < sh (qb_addr b) + kBatchSize / 8 -> outside W a.
  Proof.
    intros b a Hb Ha. pose proof BND as BB. pose proof (batch_in_space s OK b Hb) as (P1 & P2 & P3). pose proof (batch_vs_record s OK ch CHIN b Hb) as D.
    pose proof EXT as (E1 & E2 & _).
    apply (Zn_SH (qb_addr b) 1024 a); clear - Ha BB P1 P2 P3 D E1 E2; acb; zfin.
  Qed.

  Lemma Zn_B_sh : forall a, sh B <= a < sh B + kBatchSize / 8 -> outside W a.
  Proof.
    intros a Ha. pose proof BND as BB. pose proof BR as (_ & _ & _ & B16 & _). pose proof BDJ as (_ & BU & _). pose proof EXT as (E1 & E2 & E3 & _).
    apply (Zn_SH B 1024 a); clear - Ha BB B16 BU E1 E2 E3; zlets; unfold kBatchSize in *; first [tlia | Z.div_mod_to_equations; tlia].
  Qed.

  Section WithWF.
    Hypothesis WQ' : WFQ (free_st' s ch tq' cache') [] [].
    Let OKQ' : placed_ok s' /\ WFQ (a_st s') [] []. Proof. exact (conj (proj1 (proj1 R)) WQ'). Qed.
    Let LENC : length (as_cache st) = 32%nat.
    Proof. destruct WFs as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LL & _). exact LL. Qed.
    Lemma fn_pc_c : get_pc (free_st' s ch tq' cache') kBatchClass = mkPC (cnt - 1) rest.
    Proof. unfold get_pc. cbn [as_cache free_st']. unfold cache'. apply znth_upd_nth_eq. rewrite LENC. apply Nat.ltb_lt. reflexivity. Qed.
    Lemma fn_pc_o : forall c', 0 <= c' -> c' <> kBatchClass -> get_pc (free_st' s ch tq' cache') c' = get_pc st c'.
    Proof. intros c' H1 H2. unfold get_pc. cbn [as_cache free_st']. unfold cache'. apply znth_upd_nth_neq. clear - H1 H2. unfold zidx, kBatchClass in *. tlia. Qed.
    Lemma fn_pc_sub : forall c0 x, 0 <= c0 -> In x (pc_chunks (get_pc (free_st' s ch tq' cache') c0)) -> In x (pc_chunks (get_pc st c0)).
    Proof.
      intros c0 x Hc0 Hin. destruct (Z.eq_dec c0 kBatchClass) as [->|NE].
      - rewrite fn_pc_c in Hin. cbn [pc_chunks] in Hin. rewrite PCS. right. exact Hin.
      - rewrite (fn_pc_o c0 Hc0 NE) in Hin. exact Hin.
    Qed.
    Let NBIN : In nb (qc_list (as_tq (a_st s')) ++ qc_list (as_gq (a_st s'))).
    Proof. apply in_app_iff. left. change (qc_list (as_tq (a_st s'))) with (l ++ [nb]). apply in_app_iff. right. left. reflexivity. Qed.
    Lemma Zn_freech : forall c0 x a, 0 <= c0 < kNumClasses ->
      In x (rg_free_array (get_region st c0)) \/ In x (pc_chunks (get_pc (free_st' s ch tq' cache') c0)) ->
      compact_to_addr st c0 x <= a < compact_to_addr st c0 x + class_size c0 -> outside W a.
    Proof.
      intros c0 x a Hc0 Hin Ha. pose proof BND as BB.
      assert (Hin0 : In x (rg_free_array (get_region st c0)) \/ In x (pc_chunks (get_pc st c0))) by (destruct Hin as [Hin|Hin]; [left; exact Hin| right; exact (fn_pc_sub c0 x (proj1 Hc0) Hin)]).
      pose proof (freech_in_space s OK c0 x Hc0 Hin0) as (P1 & P2 & P3 & P4 & P5). pose proof (freech_vs_record s OK ch CHIN c0 x Hc0 Hin0) as D.
      pose proof EXT as (E1 & _ & E3 & _).
      assert (CV : carved st c0 (compact_to_addr st c0 x)) by (destruct Hin0; [apply carved_free| apply carved_cache]; assumption).

      pose proof (batch_not_freeQ s' [] [] OKQ' nb c0 x NBIN Hc0 Hin) as NEB.
      pose proof (carved_vs_freech s OK _ _ CVB c0 x Hc0 Hin0 (fun E => NEB (eq_sym E))) as BX. change (class_size kBatchClass) with 8192 in BX.
      pose proof (carved_vs_thread s OK _ _ CV) as CT. pose proof (carved_vs_depot s OK _ _ CV d DPL) as [CD1 CD2].
      assert (LX : compact_to_addr st c0 x + class_size c0 <= LA \/ LA + 8 <= compact_to_addr st c0 x).
      { destruct LAF as [(_ & LA0 & _)|(NE' & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & INlb)].
        - rewrite LA0. clear - P1 BB. zfin.
        - pose proof (batch_carved s OK lb INlb) as (CVl & _).
          pose proof (carved_vs_freech s OK _ _ CVl c0 x Hc0 Hin0 ltac:(hci; apply not_eq_sym; apply (batch_not_free s OK lb c0 x INlb Hc0 Hin0))) as BL.
          change (class_size kBatchClass) with 8192 in BL. clear - BL. zfin. }
      apply Zn_hi; clear - Ha BB P1 P2 D E1 E3 BX CT CD1 CD2 LX; zfin.
    Qed.
    Lemma Zn_freech_sh : forall c0 x a, 0 <= c0 < kNumClasses ->
      In x (rg_free_array (get_region st c0)) \/ In x (pc_chunks (get_pc (free_st' s ch tq' cache') c0)) ->
      sh (compact_to_addr st c0 x) <= a < sh (compact_to_addr st c0 x) + class_size c0 / 8 -> outside W a.
    Proof.
      intros c0 x a Hc0 Hin Ha. pose proof BND as BB.
      assert (Hin0 : In x (rg_free_array (get_region st c0)) \/ In x (pc_chunks (get_pc st c0))) by (destruct Hin as [Hin|Hin]; [left; exact Hin| right; exact (fn_pc_sub c0 x (proj1 Hc0) Hin)]).
      pose proof (freech_in_space s OK c0 x Hc0 Hin0) as (P1 & P2 & P3 & P4 & P5). pose proof (freech_vs_record s OK ch CHIN c0 x Hc0 Hin0) as D.
      pose proof EXT as (E1 & E2 & _).
      assert (C8 : 8 * (class_size c0 / 8) = class_size c0) by (clear - P5; Z.div_mod_to_equations; tlia).
      apply (Zn_SH (compact_to_addr st c0 x) (class_size c0 / 8) a); clear - Ha BB P1 P2 P3 P4 D E1 E2 C8; acb; zfin.
    Qed.
  Lemma Zn_farray : forall c0 a, 0 <= c0 < kNumClasses -> FA s c0 <= a < FA s c0 + rg_mapped_free_array (get_region st c0) -> outside W a.
  Proof.
    intros c0 a Hc0 Ha. pose proof BND as BB.
    pose proof (farray_in_space s OK c0 Hc0) as (P1 & P2 & P3 & P4 & P5). pose proof (farray_vs_record s OK ch CHIN c0 Hc0) as D.
    pose proof EXT as (E1 & _ & E3 & _). pose proof (carved_vs_farray s OK _ _ CVB c0 Hc0) as BX. change (class_size kBatchClass) with 8192 in BX.
    pose proof PL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & D2 & _). pose proof DPL as (_ & _ & G3 & G4 & _).
    assert (LX : FA s c0 + rg_mapped_free_array (get_region st c0) <= LA \/ LA + 8 <= FA s c0).
    { destruct LAF as [(_ & LA0 & _)|(NE' & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & INlb)].
      - rewrite LA0. clear - P1 BB. unfold FA in *. rewrite free_array_base_eq, region_beg_eq in *. zfin.
      - pose proof (batch_carved s OK lb INlb) as (CVl & _). pose proof (carved_vs_farray s OK _ _ CVl c0 Hc0) as BL.
        change (class_size kBatchClass) with 8192 in BL. clear - BL. zfin. }
    apply Zn_hi; clear - Ha BB P1 P2 D E1 E3 BX D2 G3 G4 LX; zfin.
  Qed.
  Lemma Zn_farray_sh : forall c0 a, 0 <= c0 < kNumClasses -> sh (FA s c0) <= a < sh (FA s c0) + rg_mapped_free_array (get_region st c0) / 8 -> outside W a.
  Proof.
    intros c0 a Hc0 Ha. pose proof BND as BB.
    pose proof (farray_in_space s OK c0 Hc0) as (P1 & P2 & P3 & P4 & P5). pose proof (farray_vs_record s OK ch CHIN c0 Hc0) as D.
    pose proof EXT as (E1 & E2 & _).
    apply (Zn_SH (FA s c0) (rg_mapped_free_array (get_region st c0) / 8) a); clear - Ha BB P1 P2 P3 P4 P5 D E1 E2; acb;
      (zfin || (unfold kSpaceSize, sb, st in *; Z.div_mod_to_equations; tlia)).
  Qed.
  Lemma Zn_tail : forall c0 a, 0 <= c0 < kNumClasses ->
    RB s c0 + rg_allocated_user (get_region st c0) <= a < RB s c0 + rg_mapped_user (get_region st c0) -> outside W a.
  Proof.
    intros c0 a Hc0 Ha. pose proof BND as BB.
    pose proof (tail_in_space s OK c0 Hc0) as (P1 & P2 & P3 & P4 & P5). pose proof (tail_vs_record s OK ch CHIN c0 Hc0) as D.
    pose proof EXT as (E1 & _ & E3 & _). pose proof (carved_vs_tail s OK _ _ CVB c0 Hc0) as BX. change (class_size kBatchClass) with 8192 in BX.
    pose proof PL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & D2 & _). pose proof DPL as (_ & _ & G3 & G4 & _).
    assert (LX : RB s c0 + rg_mapped_user (get_region st c0) <= LA \/ LA + 8 <= RB s c0 + rg_allocated_user (get_region st c0)).
    { destruct LAF as [(_ & LA0 & _)|(NE' & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & INlb)].
      - rewrite LA0. clear - P1 BB. unfold RB in *. rewrite region_beg_eq in *. zfin.
      - pose proof (batch_carved s OK lb INlb) as (CVl & _). pose proof (carved_vs_tail s OK _ _ CVl c0 Hc0) as BL.
        change (class_size kBatchClass) with 8192 in BL. clear - BL. zfin. }
    apply Zn_hi; clear - Ha BB P1 P2 D E1 E3 BX D2 G3 G4 LX; zfin.
  Qed.
  Lemma Zn_tail_sh : forall c0 a, 0 <= c0 < kNumClasses ->
    sh (RB s c0 + rg_allocated_user (get_region st c0)) <= a
      < sh (RB s c0 + rg_allocated_user (get_region st c0)) + (rg_mapped_user (get_region st c0) - rg_allocated_user (get_region st c0)) / 8 -> outside W a.
  Proof.
    intros c0 a Hc0 Ha. pose proof BND as BB.
    pose proof (tail_in_space s OK c0 Hc0) as (P1 & P2 & P3 & P4 & P5). pose proof (tail_vs_record s OK ch CHIN c0 Hc0) as D.
    pose proof EXT as (E1 & E2 & _).
    apply (Zn_SH (RB s c0 + rg_allocated_user (get_region st c0)) ((rg_mapped_user (get_region st c0) - rg_allocated_user (get_region st c0)) / 8) a);
      clear - Ha BB P1 P2 P3 P4 P5 D E1 E2; acb; (zfin || (unfold kSpaceSize, sb, st in *; Z.div_mod_to_equations; tlia)).
  Qed.
  Lemma Zn_rinfo : forall a, a_ri s <= a < a_ri s + kPageSize -> outside W a.
  Proof.
    intros a Ha. pose proof BND as BB. pose proof (rinfo_vs_record s OK ch CHIN) as D. pose proof EXT as (E1 & _ & E3 & _).
    pose proof (carved_vs_rinfo s OK _ _ CVB) as BX. change (class_size kBatchClass) with 8192 in BX.
    pose proof PL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & D2 & _). pose proof DPL as (_ & _ & G3 & G4 & _).
    assert (LX : a_ri s + kPageSize <= LA \/ LA + 8 <= a_ri s).
    { destruct LAF as [(_ & LA0 & _)|(NE' & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & INlb)].
      - rewrite LA0. clear - BB. zfin.
      - pose proof (batch_carved s OK lb INlb) as (CVl & _). pose proof (carved_vs_rinfo s OK _ _ CVl) as BL.
        change (class_size kBatchClass) with 8192 in BL. clear - BL. zfin. }
    unfold a_ri in *. apply Zn_hi; clear - Ha BB D E1 E3 BX D2 G3 G4 LX; unfold a_sb in *; zfin.
  Qed.
  Lemma Zn_pa : forall a, a_pa s <= a < a_pa s + kPtrArrayReserve -> outside W a.
  Proof.
    intros a Ha. pose proof BND as BB. pose proof EXT as (E1 & _ & E3 & _).
    pose proof (carved_vs_pa s OK _ _ CVB) as BX. change (class_size kBatchClass) with 8192 in BX.
    pose proof PL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & D1 & D2 & D3 & D4 & _). pose proof DPL as (_ & _ & _ & _ & _ & _ & G7 & G8 & _).
    assert (RP : a_pa s + kPtrArrayReserve <= ch_lo ch \/ ch_end ch <= a_pa s).
    { destruct (ch_primary ch) eqn:E.
      - pose proof (record_primary_space s OK ch CHIN E) as [Q1 Q2]. clear - Q1 Q2 D1. unfold a_sb, disj, kSpaceSize, kPageSize in *. tlia.
      - destruct (record_secondary_map s OK ch CHIN E) as (h & Hh & L0 & E0 & _).
        pose proof PL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SEC & _).
        pose proof (SEC h Hh) as (_ & _ & _ & _ & _ & Q & _). clear - L0 E0 Q. unfold disj in *. tlia. }
    assert (LX : a_pa s + kPtrArrayReserve <= LA \/ LA + 8 <= a_pa s).
    { destruct LAF as [(_ & LA0 & _)|(NE' & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & INlb)].
      - rewrite LA0. clear - BB. zfin.
      - pose proof (batch_carved s OK lb INlb) as (CVl & _). pose proof (carved_vs_pa s OK _ _ CVl) as BL.
        change (class_size kBatchClass) with 8192 in BL. clear - BL. zfin. }
    bands_as (_ & _ & BP & _). apply Zn_hi; clear - Ha BB E1 E3 BX D4 G7 G8 RP LX BP; zfin.
  Qed.
  Lemma Zn_sechdr : forall h a, In h (as_sec st) -> sc_map_beg h <= a < sc_map_beg h + kPageSize -> outside W a.
  Proof.
    intros h a Hh Ha. pose proof BND as BB. pose proof EXT as (E1 & _ & E3 & _ & _ & _ & _ & E8 & E9 & E10).
    pose proof (carved_vs_sec s OK _ _ CVB h Hh) as BX. change (class_size kBatchClass) with 8192 in BX.
    pose proof PL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SEC & SEC2 & _).
    pose proof (SEC h Hh) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9). pose proof DPL as (_ & _ & _ & _ & _ & _ & _ & _ & G9 & _). destruct (G9 h Hh) as [Gh1 Gh2].
    pose proof (aapp_lit _ _ Q2) as Q2b. apply aapp_env in Q2; [| unfold kPageSize in Q4; clear - Q4; tlia].
    assert (RP : sc_map_beg h + kPageSize <= U - 16 \/ U + 8 <= sc_map_beg h).
    { destruct (ch_primary ch) eqn:E.
      - pose proof (sechdr_vs_primary_record s OK ch CHIN h Hh E) as D. clear - D E1 E3. tlia.
      - destruct (record_secondary_map s OK ch CHIN E) as (h0 & Hh0 & L0 & E0 & A0).
        destruct (Z.eq_dec (sc_map_beg h) (sc_map_beg h0)) as [EQ|NE].
        + left. rewrite EQ. clear - A0 E8 E9. tlia.
        + pose proof (SEC2 h h0 Hh Hh0 NE) as D. clear - D L0 E0 E1 E3 Q4. unfold disj, kPageSize in *. tlia. }
    assert (LX : sc_map_beg h + sc_map_size h <= LA \/ LA + 8 <= sc_map_beg h).
    { destruct LAF as [(_ & LA0 & _)|(NE' & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & INlb)].
      - rewrite LA0. clear - Q2. zfin.
      - pose proof (batch_carved s OK lb INlb) as (CVl & _). pose proof (carved_vs_sec s OK _ _ CVl h Hh) as BL.
        change (class_size kBatchClass) with 8192 in BL. clear - BL. zfin. }
    apply Zn_hi; clear - Ha BB Q2 Q2b Q3 Q4 Q7 BX Gh1 Gh2 RP LX; zfin.
  Qed.

  Lemma Zn_thr : forall a, TH <= a < TH + 2800 -> ~ (TH + 80 <= a < TH + 112) -> ~ (TH + 2128 <= a < TH + 2132) -> ~ (TH + 2784 <= a < TH + 2792) ->
    outside W a.
  Proof.
    intros a Ha N1 N2 N3. pose proof BND as BB. pose proof (free_plu s m ch d R CHIN DPL) as (PU & _). pose proof DPL as (G1 & G2 & _). fold TH in G1, G2.
    pose proof BDJ as (BTB & _). bands_as (BT & _).
    assert (LX : TH + 4096 <= LA \/ LA + 8 <= TH).
    { destruct LAF as [(_ & LA0 & _)|(NE' & _ & _ & _ & LT & _)]; [rewrite LA0; clear - BB; zfin| clear - LT; zfin]. }
    apply Zn_core; try assumption; clear - Ha N1 N2 N3 BB PU G1 G2 LX BTB BT; unfold AIAINIT, AIAINST, disj, kPageSize, kBatchSize in *; zlets; acb; try tlia.
    all: unfold sh, ASHADOW_BASE; Z.div_mod_to_equations; tlia.
  Qed.
  Lemma Zn_ctx : forall a, CTX + 8 <= a < CTX + 160 -> outside W a.
  Proof.
    intros a Ha. pose proof BND as BB. pose proof PURE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Y6 & _).
    pose proof (free_plu s m ch d R CHIN DPL) as (_ & PU & _). pose proof DPL as (_ & _ & _ & _ & G5 & G6 & _).
    pose proof (carved_vs_ctx s OK _ _ CVB) as BX. change (class_size kBatchClass) with 8192 in BX.
    assert (LX : CTX + 160 <= LA \/ LA + 8 <= CTX).
    { destruct LAF as [(_ & LA0 & _)|(NE' & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & INlb)].
      - rewrite LA0. clear - BB. zfin.
      - pose proof (batch_carved s OK lb INlb) as (CVl & _). pose proof (carved_vs_ctx s OK _ _ CVl) as BL.
        change (class_size kBatchClass) with 8192 in BL. clear - BL. zfin. }
    bands_as (_ & BC & _). apply Zn_hi; clear - Ha BB Y6 PU G5 G6 BX LX BC; zfin.
  Qed.

  Let TQL : qc_list tq' = l ++ [nb] /\ qc_bytes tq' = qc_bytes tq + size + kBatchSize. Proof. split; reflexivity. Qed.

  Let NLA : forall b, In b (removelast l ++ qc_list (as_gq st)) -> qb_addr b <> LA.
  Proof.
    intros b Hb E. destruct LAF as [(EL & LA0 & _)|(NE & _)].
    - rewrite EL in Hb. cbn [removelast app] in Hb. assert (INb : In b (qc_list (as_tq st) ++ qc_list (as_gq st))) by (apply in_app_iff; right; exact Hb).
      pose proof (batch_in_space s OK b INb) as (P1 & _). pose proof BND as BB. rewrite LA0 in E. clear - P1 BB E. zfin.
    - pose proof (app_removelast_last (mkQB 0 0 0 []) NE) as LSPLIT. fold lb in LSPLIT.
      pose proof (batch_addrs_nodup s OK) as ND. fold st in ND. fold tq in ND. fold l in ND. rewrite LSPLIT, <- app_assoc, map_app in ND at 1.
      apply in_app_iff in Hb. destruct Hb as [Hb|Hb].
      + eapply (NoDup_app_disjoint _ _ (qb_addr b) ND); [apply in_map_iff; exists b; auto|]. cbn [map app]. left. fold LA. symmetry. exact E.
      + apply NoDup_app_r in ND. cbn [map app] in ND. apply NoDup_cons_iff in ND. destruct ND as [NI _]. apply NI. fold LA. rewrite <- E. apply in_map_iff. exists b; auto.
  Qed.

  Lemma thread_after_new : thread_rep s' m'.
  Proof.
    pose proof TQL as [E1 E2].
    assert (EQ : [C8 (wz (zlen (qc_list tq'))); C8 (wz (hd 0 (map qb_addr (qc_list tq')))); C8 (wz (last (map qb_addr (qc_list tq')) 0)); C8 (wz (qc_bytes tq'))]
               = [C8 (wz (k + 1)); C8 (wz (if k =? 0 then B else hd 0 (map qb_addr l))); C8 (wz B); C8 (wz (qc_bytes tq + (size + kBatchSize)))]).
    { rewrite E1, E2, map_app. cbn [map qb_addr nb]. unfold nb. cbn [qb_addr]. rewrite hd_map_app_single, last_app1.
      do 3 f_equal; [unfold k, zlen; rewrite length_app; cbn [length]; clear; tlia|]. f_equal. f_equal. f_equal. clear. tlia. }
    apply (thread_after s ch m m' P tq' cache' L' S' AL' R CHIN UHI AG WM TST' UNW').
    - apply (junk_of_rw_cells m' _ [C8 j0; C8 j1; C8 j2; C8 j3]); [exact STATS'| reflexivity].
    - rewrite EQ. exact TQc'.
    - intros a Ha. apply Zn_thr; unfold OT_TQ in Ha; clear - Ha; tlia.
    - intros a Ha. apply Zn_thr; unfold OT_TQ, OT_CACHE in Ha; clear - Ha; tlia.
    - intros a Ha; apply Zn_ctx; clear - Ha; tlia.
    - intros a Ha; apply Zn_ctx; clear - Ha; tlia.
  Qed.

  Lemma pclass24_after_new : pclass_rep s' m' kBatchClass.
  Proof.
    pose proof R as RR; destruct RR as (_ & _ & _ & _ & _ & _ & CL & _). destruct (CL kBatchClass HC24) as (_ & PC & _ & _).
    unfold pclass_rep in PC |- *. change (a_st s') with (free_st' s ch tq' cache'). rewrite fn_pc_c. cbn [pc_count pc_chunks].
    change (as_cache_inited (free_st' s ch tq' cache')) with (as_cache_inited st). change (a_cache s') with (a_cache s).
    fold st in PC. rewrite PCS in PC. fold cnt in PC. destruct PC as (Q1 & Q2 & Q3 & Q4).
    assert (EA : a_cache s + PCLASS_SIZE * kBatchClass = TH + 2128) by (unfold a_cache, OT_CACHE, PCLASS_SIZE, kBatchClass; zlets; tlia). rewrite EA in *.
    apply (proj1 (rw_cells_app asegs _ _ [_] [_])) in Q1. destruct Q1 as [_ Q1b]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat] in Q1b.
    split. { apply (proj2 (rw_cells_app asegs _ _ [_] [_])). split; [exact PC1'|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat].
             eapply (rw_cells_transport_pt P m m' AG WM); [exact Q1b|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
             intros a Ha. apply Zn_thr; clear - Ha; zlets; tlia. }
    split. { eapply (rw_cells_transport_pt P m m' AG WM); [exact Q2|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
             intros a Ha. apply Zn_thr; clear - Ha; zlets; tlia. }
    split; [replace (TH + 2128 + 16) with (TH + 2144) by tlia; exact PC3'|].
    intros _. replace (TH + 2128 + 16 + 4 * (cnt - 1) + (64 - 4 * (cnt - 1))) with (TH + 2208) by tlia.
    replace (TH + 2128 + 16) with (TH + 2144) by tlia. exact PC4'.
  Qed.

  Lemma batches_after_new : batches_rep m' (qc_list tq') /\ batches_rep m' (qc_list (as_gq st)).
  Proof.
    pose proof TQL as [E1 _]. rewrite E1. pose proof R as RR. destruct RR as (_ & _ & _ & _ & _ & _ & CL & _ & BT & BG). fold st tq l in BT. fold st in BG.

    assert (NBR : batch_rep m' nb 0).
    { unfold batch_rep, nb. cbn [qb_addr qb_size qb_count qb_chunks].
      apply (proj1 (rw_cells_app asegs _ _ [_; _; _] [_])) in NB'. destruct NB' as [NB3 NB4]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in NB4.
      split; [exact NB3|].
      split. { cbn [wlist map]. apply u64arr_one. unfold ch_chunk_beg, kChunkHeaderSize. fold U. replace (U - 16) with (U + -16) by tlia. exact NB4. }
      split. { intros _. replace (B + 24 + 8 * 1) with (B + 32) by tlia. replace (B + 32 + (kBatchSize - 24 - 8 * 1)) with (B + kBatchSize) by tlia. exact NBJ'. }
      destruct (CL kBatchClass HC24) as (_ & _ & RSH & _). destruct RSH as (_ & H2 & _). specialize (H2 cp CPIN). fold st B in H2.
      change (class_size kBatchClass / 8) with (kBatchSize / 8) in H2.
      eapply (poisoned_transport_pt P m m' AG WM); [exact H2|]. change (Z.of_nat (Z.to_nat (kBatchSize / 8))) with (kBatchSize / 8). exact Zn_B_sh. }
    split.
    - destruct LAF as [(EL & _ & K0)|(NE & K1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & INlb)].
      + rewrite EL. cbn [app batches_rep map hd]. split; [exact NBR| exact I].
      + pose proof (app_removelast_last (mkQB 0 0 0 []) NE) as LSPLIT. fold lb in LSPLIT.
        assert (GEN : forall r, (forall b, In b r -> In b (removelast l)) -> batches_rep m (r ++ [lb]) -> batches_rep m' (r ++ [lb; nb])).
        { induction r as [|x r IH]; intros SUB BRr.
          - cbn [batches_rep app map hd] in BRr |- *. destruct BRr as [BR1 _]. split; [| split; [exact NBR| exact I]].

            unfold batch_rep in BR1 |- *. unfold nb. cbn [qb_addr]. fold LA. destruct BR1 as (C1 & C2 & C3 & C4).
            pose proof (WF_batch _ lb WFs INlb) as (Cb1 & Cb2 & _). unfold zlen in Cb1.
            apply (proj1 (rw_cells_app asegs _ _ [_] [_; _])) in C1. destruct C1 as [_ C1b]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in C1b.
            split. { apply (proj2 (rw_cells_app asegs _ _ [_] [_; _])). split; [apply LAn'; clear - K1; tlia|].
                     cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
                     eapply (rw_cells_transport_pt P m m' AG WM); [exact C1b|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
                     intros a Ha. apply (Zn_lastbatch a NE). unfold kBatchSize. clear - Ha. tlia. }
            split. { eapply (u64arr_transport_pt P m m' AG WM); [exact C2|]. unfold wlist. rewrite length_map.
                     intros a Ha. apply (Zn_lastbatch a NE). unfold kBatchSize, kBatchCount in *. clear - Ha Cb1 Cb2. tlia. }
            split. { eapply (junk_transport_pt P m m' AG WM); [exact C3|]. intros a Ha. apply (Zn_lastbatch a NE). unfold kBatchSize, kBatchCount in *. clear - Ha Cb1 Cb2. tlia. }
            eapply (poisoned_transport_pt P m m' AG WM); [exact C4|]. change (Z.of_nat (Z.to_nat (kBatchSize / 8))) with (kBatchSize / 8).
            intros a Ha. exact (Zn_batch_sh lb a INlb Ha).
          - cbn [batches_rep app] in BRr |- *. destruct BRr as [BX BR2]. split.
            + rewrite (hd_map_app_cons r lb [nb] []).
              assert (INx : In x (qc_list (as_tq st) ++ qc_list (as_gq st))).
              { apply in_app_iff. left. fold tq. fold l. rewrite LSPLIT. apply in_app_iff. left. apply SUB. left. reflexivity. }
              apply (batch_after s m m' P R AG WM x _ INx BX).
              * intros a Ha. apply (Zn_batch x a INx); [| exact Ha]. apply NLA. apply in_app_iff. left. apply SUB. left. reflexivity.
              * intros a Ha. exact (Zn_batch_sh x a INx Ha).
            + apply IH; [intros b Hb; apply SUB; right; exact Hb| exact BR2]. }
        rewrite LSPLIT at 1. rewrite <- app_assoc. cbn [app]. apply GEN; [intros b Hb; exact Hb|]. rewrite <- LSPLIT. exact BT.
    - apply (batches_after_list s m m' P R AG WM (qc_list (as_gq st))); [intros b Hb; apply in_app_iff; right; exact Hb| exact BG| |].
      + intros b a Hb Ha. apply (Zn_batch b a ltac:(apply in_app_iff; right; exact Hb)); [| exact Ha]. apply NLA. apply in_app_iff. right. exact Hb.
      + intros b a Hb Ha. exact (Zn_batch_sh b a ltac:(apply in_app_iff; right; exact Hb) Ha).
  Qed.

  Lemma regions_after_new : forall c0, 0 <= c0 < kNumClasses ->
    region_rep s' m' c0 /\ pclass_rep s' m' c0 /\ region_shadow_rep s' m' c0 /\ region_junk_rep s' m' c0.
  Proof.
    intros c0 Hc0. split; [| split; [| split]].
    - apply (region_after s ch m m' P tq' cache' L' S' AL' R [] [] WQ' AG WM c0 Hc0 Zn_rinfo (fun a Ha => Zn_farray c0 a Hc0 Ha) (fun a Ha => Zn_tail c0 a Hc0 Ha)).
    - destruct (Z.eq_dec c0 kBatchClass) as [->|NE]; [exact pclass24_after_new|].
      apply (pclass_after s ch m m' P tq' cache' L' S' AL' R AG WM c0 Hc0 (fn_pc_o c0 (proj1 Hc0) NE)).
      intros a Ha. apply Zn_thr; unfold a_cache, OT_CACHE, PCLASS_SIZE, kNumClasses, kBatchClass in *; clear - Ha Hc0 NE; zlets; tlia.
    - apply (region_shadow_after s ch m m' P tq' cache' L' S' AL' R [] [] WQ' AG WM c0 Hc0 (fun x H => fn_pc_sub c0 x (proj1 Hc0) H)
               (fun x a Hin Ha => Zn_freech_sh c0 x a Hc0 Hin Ha) (fun a Ha => Zn_tail_sh c0 a Hc0 Ha) (fun a Ha => Zn_farray_sh c0 a Hc0 Ha)).
    - apply (region_junk_after s ch m m' P tq' cache' L' S' AL' R AG WM c0 Hc0 (fun x H => fn_pc_sub c0 x (proj1 Hc0) H)
               (fun x a Hin Ha => Zn_freech c0 x a Hc0 Hin Ha)).
  Qed.

  Lemma armem_after_new : ARmem s' m'.
  Proof.
    destruct batches_after_new as [BT' BG'].
    split. { apply (inst_after s ch m m' P tq' cache' L' S' AL' R AG WM).
             intros a Ha. apply Zn_static; [unfold astatic; left; exact Ha| |]; unfold AINST, OI_MISMATCH, AIAINIT, AIAINST in *; clear - Ha; tlia. }
    split; [exact (flags_after s ch m m' P tq' cache' L' S' AL' R AG WM FLG' Zn_flags)|].
    split; [exact thread_after_new|].
    split; [exact (sec_after s ch m m' P tq' cache' L' S' AL' R [] [] WQ' AG WM Zn_pa Zn_sechdr)|].
    split; [unfold ia_rep; change (as_internal_init (a_st s')) with true; exact IA'|].
    split; [exact regions_after_new|].
    split; [exact (chunks_after s ch m m' P tq' cache' L' S' AL' b1 actx idv bs R CHIN ALLOC UHI AG WM B1 HDR' UW' SHF' BLK
                     Zn_rec_self Zn_rec_self_sh Zn_rec_other Zn_rec_other_sh)|].
    exact (conj BT' BG').
  Qed.
  Lemma arepq_after_new : AREPQ s' [] [] m'.
  Proof. split; [exact (proj1 (proj1 R))|]. split; [exact WQ'| exact armem_after_new]. Qed.

  End WithWF.
End FreeNewPost.
End HCW.
