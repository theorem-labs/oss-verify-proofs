(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FMapPositive.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import AsanAllocModel LazyRestrict.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AllocWf AllocKit AllocRep AllocRepFacts AllocRepFacts2 AllocRepX
     AsDepotInv AsDepotHash AsDepotPut AW_DepotFrame AW_MallocBase AW_AllocBase AW_LargeAlloc1 AW_InitCache AW_IAInit AW_FreePre AW_Enqueue2 AS_Free1 AllocWalkKit
     AG_MallocModel AG_WFHit AG_Malloc AG_Malloc2 AG_RefillModel AS_Refill1 AG_Refill1 AG_Refill2 AG_MallocCold
     AG_FreeModel AG_WFFree AG_Free1 AG_FreeFacts AG_Free2 AG_Free3 AG_Free4 AG_Free5 AG_Free6 AG_RepQ.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import PerfLia.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
(* [comment removed for export] *)
Ltac lia ::=
  dle_wrap ltac:(first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ]).

Section HCW.
  Context {HCEIL : HeapCeil}.

Lemma agree_on_sym : forall (P : Z -> Prop) ma mb, agree_on P ma mb -> agree_on P mb ma.
Proof. intros P ma mb AG x Hx Hr. symmetry. exact (AG x Hx Hr). Qed.
Lemma agree_on_weaken : forall (P P' : Z -> Prop) ma mb, agree_on P ma mb -> (forall a, P' a -> P a) -> agree_on P' ma mb.
Proof. intros P P' ma mb AG SUB x Hx Hr. exact (AG x (SUB x Hx) Hr). Qed.

Ltac trq AG WM H ZT := eapply (rw_cells_transport_pt _ _ _ AG WM); [exact H|];
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul Z.mul length];
  let Ha := fresh in intros ? Ha; apply ZT; clear - Ha; tlia.
(* [comment removed for export] *)
Lemma flagsx_pt : forall (P : Z -> Prop) ma mb, agree_on P ma mb -> wmono asegs ma mb ->
  (forall a, (a < 7849928 \/ 7849956 <= a < 7915480 \/ 12109808 <= a < 12599296) -> ~ (AIAINIT <= a < AIAINIT + 4) -> ~ (AIAINST <= a < AIAINST + 0x81030) -> P a) ->
  flagsx_rep ma -> flagsx_rep mb.
Proof.
  intros P ma mb AG WM ZT FX.
  destruct FX as (FXa & FXb & [g FXc] & FXd & [bb FXe]). unfold flagsx_rep, ALIBCPGSZ, AGOT_SSP, ASSPGUARD, ACFLAGS, AIAINIT, AIAINST in *.
  split; [trq AG WM FXa ZT|]. split; [trq AG WM FXb ZT|]. split; [exists g; trq AG WM FXc ZT|]. split; [trq AG WM FXd ZT|]. exists bb; trq AG WM FXe ZT.
Qed.

(* [comment removed for export] *)
Lemma hd_batch_word : forall s m, AREP s m -> 0 <= hd 0 (map qb_addr (qc_list (as_tq (a_st s)))) < 2^64.
Proof.
  intros s m R. pose proof (proj1 R) as OK. destruct (qc_list (as_tq (a_st s))) as [|b r] eqn:E; [cbn; tlia|]. cbn [map hd].
  assert (Hb : In b (qc_list (as_tq (a_st s)) ++ qc_list (as_gq (a_st s)))) by (apply in_app_iff; left; rewrite E; left; reflexivity).
  pose proof (batch_in_space s OK b Hb) as (P1 & P2 & _). pose proof (proj1 OK) as (S1 & S2 & S3 & _). acb. unfold AHI_LO, kSpaceSize, kPageSize, kBatchSize in *. tlia.
Qed.
End HCW.

Section FreeRefillFacts.
  Context {HCEIL : HeapCeil}.
  Ltac trq AG WM H ZT := eapply (rw_cells_transport_pt _ _ _ AG WM); [exact H|];
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul Z.mul length];
  let Ha := fresh in intros ? Ha; apply ZT; clear - Ha; tlia.
  Variables (s : ast) (m : mem) (d : depot) (lo spv : Z) (ch : chunk) (bs : list byte).

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
  (* [comment removed for export] *)
  Let c := kBatchClass.
  Let CA := TH + 208.
  Let P := CA + 80 * c.
  Let RI := a_ri s + 128 * c.
  Let r := get_region st c.
  Let nf := rg_num_freed r. Let mfa := rg_mapped_free_array r. Let au := rg_allocated_user r. Let mu := rg_mapped_user r. Let fl := rg_free_array r.
  Let n := rf_n c.
  Let mu' := rf_mu' c nf au mu. Let nnew := rf_nnew c nf au mu. Let nf1 := rf_nf1 c nf au mu. Let mfa' := rf_mfa' c nf mfa au mu.
  Let au' := rf_au' c nf au mu. Let fl1 := rf_fl1 c nf au mu fl.
  Let st2 := refilled st c.
  Let chunks2 := firstn (Z.to_nat n) fl1.
  Let cp := hd 0 chunks2.
  Let B := compact_to_addr st2 c cp.
  Variables (L2 S2 : list (word * word)) (AL' : Z).
  Let sR := mkAst st2 (a_thr s) (a_ctx s) (a_fsb s) L2 S2 (a_Zr s) AL' (a_top s) (a_bot s).
  (* [comment removed for export] *)
  Let tq' := tq_new tq B (ch_chunk_beg ch) size.
  Let cache' := upd_nth (as_cache st2) (zidx c) (mkPC (n - 1) (tl chunks2)).
  Let sF := free_s' sR ch tq' cache' L2 S2 AL'.
  (* [comment removed for export] *)
  Let Wh : list ivl := free_head_W lo spv TH U size d.
  Let Wf : list ivl := rf_W lo (spv + -2272) P RI (FA s c) (RB s c) TH CA nf mfa mu mfa' mu'.
  Let WR : list ivl := (lo, spv) :: (TH + 3168, TH + 3169) :: rf_W lo spv P RI (FA s c) (RB s c) TH CA nf mfa mu mfa' mu'.
  Let Wn : list ivl := enq_new_W lo spv TH B LA.
  Let Wo : list ivl := [(AIAINIT, AIAINIT + 4); (AIAINST, AIAINST + 0x81030); (U + -16, U + -12); (U, U + 8); (sh U, sh U + nsh size)] ++ depot_W d.

  Hypothesis R : AREP s m.
  Hypothesis CHIN : In ch (chunk_list st).
  Hypothesis ALLOC : ch_state ch = CAllocated.
  Hypothesis UHI : aapp (ch_user_beg ch - 16) (16 + round_up (ch_used ch) 8).   (* [comment removed for export] *)
  Hypothesis DPL : depot_placed s d.
  Hypothesis LO : aceil <= lo.
  Hypothesis HI : lo + 2944 <= spv.
  Hypothesis DLO : d_nb d + 16 * 65536 <= lo /\ d_sb d + 8 * 131072 <= lo.
  Hypothesis MISS : pc_count (get_pc st c) = 0.
  Hypothesis ROOM : mu + 2 * kUserMapSize <= kFreeArrayOffset.
  Hypothesis NN : need_new tq = true.
  Hypothesis NOD : qc_bytes tq + size + kBatchSize <= kMaxCacheSize.
  Hypothesis QSZ : size <= kQuarantineMaxSize /\ size < 2^32.
  Hypothesis BLK : rw_cells asegs m U [CB (Z.to_nat size) bs].

  Ltac zlets := repeat match goal with H := _ |- _ => subst H end.
  Ltac zfin := zlets; unfold AHI_LO, AIMG_TOP, ALOWSH_LO, OT_TQ, OT_CACHE, a_ri, a_sb, disj, kPageSize, kBatchSize, kSpaceSize, kPtrArrayReserve in *; tlia.

  Let OK : ast_ok s. Proof. exact (proj1 R). Qed.
  Let PL : placed_ok s. Proof. exact (proj1 OK). Qed.
  Let WFs : WF st. Proof. exact (proj2 OK). Qed.
  Let HC : 1 <= c <= 30. Proof. unfold c, kBatchClass. tlia. Qed.
  Let HCK : 0 <= c < kNumClasses. Proof. unfold c, kBatchClass, kNumClasses. tlia. Qed.
  Let PURE := free_pure s m ch R CHIN UHI.
  Let RPURE := refill_pure s m c R HC MISS.
  Let RF := rf_facts st c WFs HC ROOM.
  Let WF2 : WF st2. Proof. exact (WF_refill st c WFs HC MISS ROOM). Qed.
  Let PCc := rfd_pc_c st c WFs HC ROOM.
  Let EXT : ch_lo ch <= U - 16 /\ U + round_up size 8 <= ch_end ch /\ U + 8 <= ch_end ch /\ 12599296 <= ch_lo ch /\ ch_end ch <= aceil
            /\ ch_lo ch mod 8 = 0 /\ ch_end ch mod 8 = 0 /\ ch_alloc_beg ch + ch_rz ch = U /\ 16 <= ch_rz ch /\ ch_lo ch <= ch_alloc_beg ch.
  Proof.
    pose proof (record_ext s OK ch CHIN) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9).
    pose proof (chunk_geom s OK ch CHIN) as (G1 & G2 & G3 & G4 & G5 & G6 & _).
    pose proof (record_band s OK ch CHIN) as RB'. unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AIMG_TOP, AHI_LO in RB'. unfold AHI_LO in UHI.
    clear - X1 X2 X3 X4 X5 X6 X7 X8 X9 G1 G2 G3 G4 G5 G6 RB' UHI. subst U size. pose proof (aapp_env _ _ UHI ltac:(clear - G3 G5; tlia)) as [UE _]. unfold AHI_LO, AIMG_TOP in *. repeat split; try assumption; tlia.
  Qed.
  Let NR : n = 1. Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Let BND : aceil <= lo /\ 4096 <= TH /\ TH + 4096 <= aceil /\ TH mod 4096 = 0 /\ 12599296 <= CTX /\ CTX + 160 <= aceil
            /\ 0x10007fff8000 <= sb /\ sb + 137438953472 + 4096 <= aceil /\ sb mod 65536 = 0 /\ 12599296 <= a_pa s /\ a_pa s + 8388608 <= aceil
            /\ 12599296 <= d_nb d /\ d_nb d + 16 * 65536 <= aceil /\ 12599296 <= d_sb d /\ d_sb d + 8 * 131072 <= aceil
            /\ 4096 <= a_top s <= 2^47 /\ 0 <= a_bot s < a_top s
            /\ P = TH + 208 + 80 * c /\ CA = TH + 208 /\ RI = sb + 137438953472 + 128 * c /\ RB s c = sb + c * 4294967296 /\ FA s c = RB s c + 3758096384 /\ c = 24.
  Proof.
    pose proof PL as (Y1 & Y2 & Y3 & P1 & P2 & P3 & T1 & T2 & T3 & X1 & X2 & X3 & D1 & D2 & D3 & D4 & D5 & F1 & F2 & D6 & D7 & D8 & D9 & SEC & SEC2 & TCX).
    pose proof DPL as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
    assert (E1 : RB s c = sb + c * 4294967296) by (unfold RB, sb, a_sb; rewrite region_beg_eq; reflexivity).
    assert (E2 : FA s c = RB s c + 3758096384) by (unfold FA, RB; rewrite free_array_base_eq; reflexivity).
    apply akobj_env in T2; [| unfold kPageSize; clear; tlia]. apply aapp_env in X2; [| clear; tlia]. apply aapp_env in P2; [| unfold kPtrArrayReserve; clear; tlia].
    apply aapp_env in G10; [| clear; tlia]. apply aapp_env in G12; [| clear; tlia].
    clear - Y1 Y2 Y3 P1 P2 P3 T1 T2 T3 X1 X2 X3 TCX G10 G11 G12 G13 LO E1 E2. unfold TH, sb, CTX, P, CA, RI, a_ri, c. unfold a_sb in *.
    acb. unfold AHI_LO, AIMG_TOP, kSpaceSize, kPageSize, kPtrArrayReserve, kBatchClass in *. repeat split; tlia.
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
  Let BU : 12599312 <= U /\ U + round_up size 8 <= aceil /\ 1 <= size /\ size <= round_up size 8 /\ round_up size 8 = 8 * nsh size
           /\ U mod 16 = 0 /\ 2148314624 <= sh U /\ sh U + nsh size <= 0x10007fff8000 /\ size < 2^32.   (* [comment removed for export] *)
  Proof.
    pose proof PURE as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & _). pose proof (proj2 QSZ) as Q2.
    clear - Z1 Z2 Z3 Z4 Z5 Z6 Q2. zlets. destruct Z2 as (ZA & _ & ZB). unfold aapp, aapp_lo, aapp_hi, AIMG_TOP, ALOWSH_LO, AHI_LO in ZA, ZB. unfold AHI_LO in *. acb.
    assert (SH : 2148314624 <= sh (ch_user_beg ch) /\ sh (ch_user_beg ch) + nsh (ch_used ch) <= 0x10007fff8000).
    { clear - ZA Z3 Z6 Z1 ACEILB. unfold sh, ASHADOW_BASE. Z.div_mod_to_equations. tlia. }
    clear ZA. repeat match goal with |- _ /\ _ => split end; tlia.
  Qed.
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
  Let BDJ : (TH + 4096 <= sb \/ sb + 137438953472 + 4096 <= TH) /\ (TH + 4096 <= CTX \/ CTX + 160 <= TH) /\ (CTX + 160 <= sb \/ sb + 137438953472 + 4096 <= CTX)
            /\ (TH + 4096 <= d_nb d \/ d_nb d + 1048576 <= TH) /\ (TH + 4096 <= d_sb d \/ d_sb d + 1048576 <= TH)
            /\ (sb + 137438953472 + 4096 <= d_nb d \/ d_nb d + 1048576 <= sb) /\ (sb + 137438953472 + 4096 <= d_sb d \/ d_sb d + 1048576 <= sb)
            /\ (TH + 4096 <= U - 16 \/ U + 8 <= TH) /\ (CTX + 160 <= U - 16 \/ U + 8 <= CTX)
            /\ (d_nb d + 16 * 65536 <= U - 16 \/ U + 8 <= d_nb d) /\ (d_sb d + 8 * 131072 <= U - 16 \/ U + 8 <= d_sb d).
  Proof.
    pose proof PL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & D1 & D2 & D3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TCX).
    pose proof DPL as (G1 & G2 & G3 & G4 & _). pose proof (free_plu s m ch d R CHIN DPL) as (U1 & U2 & U3 & U4).
    clear - D2 D3 TCX G1 G2 G3 G4 U1 U2 U3 U4. zlets. unfold disj, a_sb, kSpaceSize, kPageSize in *. repeat split; tlia.
  Qed.
  (* [comment removed for export] *)
  Let BR : 0 <= nf /\ 4 * nf <= mfa /\ mfa <= 536870912 /\ 0 <= au <= mu /\ mu + 262144 <= 3758096384 /\ Z.of_nat (length (wlist (rev fl))) = nf
           /\ mu <= mu' <= mu + 262144 /\ mfa <= mfa' <= mfa + 262144 /\ mfa' <= 536870912 /\ n = 1 /\ n <= nf1 /\ 4 * nf1 <= mfa' /\ au <= au' <= mu'
           /\ zlen fl1 = nf1 /\ 0 <= nnew.
  Proof.
    pose proof RPURE as (U1 & U2 & U3 & U4 & U5 & U6 & U7 & U8 & U9 & U10 & PCS).
    pose proof RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13 & Q14 & Q15).
    pose proof (rf_mfa_delta st c WFs HC ROOM) as FD.
    fold st r in U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, Q1, Q2, Q3, Q4, Q5, Q6, Q7, Q11, Q12, FD. fold nf mfa au mu fl n in U1, U2, U4, U5, U8, Q1, Q2, Q3, Q4, Q5, Q6, Q7, Q11, Q12, FD.
    fold mu' nnew nf1 mfa' au' fl1 in Q1, Q2, Q3, Q4, Q5, Q6, Q7, Q11, Q12, FD.
    unfold kFreeArraySize, kUserMapSize, kFreeArrayOffset, kFreeArrayMapSize in *.
    clear - U1 U2 U4 U5 U8 Q1 Q2 Q3 Q4 Q6 Q7 Q11 Q12 FD NR. repeat split; tlia.
  Qed.
  Let SHB : 0x2008fff7000 <= sh (RB s c + mu) /\ sh (RB s c + mu) + (mu' - mu) / 8 <= sh aceil
              /\ 0x2008fff7000 <= sh (FA s c + mfa) /\ sh (FA s c + mfa) + (mfa' - mfa) / 8 <= sh aceil /\ sh aceil <= 0x10007fff8000 - 4096 / 8.
  Proof. pose proof BND as B0. pose proof BR as B1. clear - B0 B1. acb. unfold sh, ASHADOW_BASE. Z.div_mod_to_equations. tlia. Qed.
  Let ALN : (RB s c + mu) mod 8 = 0 /\ 8 * ((mu' - mu) / 8) = mu' - mu /\ (FA s c + mfa) mod 8 = 0 /\ 8 * ((mfa' - mfa) / 8) = mfa' - mfa /\ U mod 8 = 0.
  Proof.
    pose proof BND as (_ & _ & _ & _ & _ & _ & _ & _ & SB64 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ERB & EFA & _). pose proof BU as (_ & _ & _ & _ & _ & U16 & _).
    pose proof RF as (_ & _ & _ & _ & _ & _ & _ & Q8 & _ & _ & _ & _ & Q13 & _). pose proof RPURE as (_ & _ & U3 & _ & _ & U6 & _).
    fold st r in Q8, Q13, U3, U6. fold nf mfa au mu in Q8, Q13, U3, U6. fold mu' mfa' in Q8, Q13.
    unfold kUserMapSize, kFreeArrayMapSize in *. clear - SB64 ERB EFA U16 Q8 Q13 U3 U6.
    destruct (proj1 (Z.mod_divide sb 65536 ltac:(tlia)) SB64) as [t Ht].
    destruct (proj1 (Z.mod_divide mfa 262144 ltac:(tlia)) U3) as [f Hf]. destruct (proj1 (Z.mod_divide mu 262144 ltac:(tlia)) U6) as [u Hu].
    destruct (proj1 (Z.mod_divide mfa' 262144 ltac:(tlia)) Q13) as [f' Hf']. destruct (proj1 (Z.mod_divide mu' 262144 ltac:(tlia)) Q8) as [u' Hu'].
    rewrite EFA, ERB. repeat split; Z.div_mod_to_equations; nia.
  Qed.

  (* [comment removed for export] *)
  Let LAF : (l = [] /\ LA = 0 /\ k = 0)
            \/ (l <> [] /\ 1 <= k /\ AHI_LO <= LA /\ LA + kBatchSize <= aceil /\ (TH + 4096 <= LA \/ LA + kBatchSize <= TH)
                /\ (LA + kBatchSize <= U - 16 \/ U + 8 <= LA)
                /\ (d_nb d + 16 * 65536 <= LA \/ LA + kBatchSize <= d_nb d) /\ (d_sb d + 8 * 131072 <= LA \/ LA + kBatchSize <= d_sb d)
                /\ sb + kBatchClass * 2^32 <= LA /\ LA + kBatchSize <= sb + kBatchClass * 2^32 + kFreeArrayOffset
                /\ In lb (qc_list (as_tq st) ++ qc_list (as_gq st)) /\ kBatchCount <= qb_count lb /\ qb_count lb <= kBatchCount
                /\ LA + kBatchSize <= RB s c + au).
  Proof.
    assert (D : l = [] \/ l <> []) by (destruct l; [left; reflexivity| right; discriminate]).
    destruct D as [EL|NE].
    - left. split; [exact EL|]. unfold LA, lb, k. rewrite EL. split; reflexivity.
    - right.
      pose proof (free_last_cells s m ch d R CHIN DPL NE) as (_ & _ & _ & INlb & _ & CB & K1 & LA1 & LA2 & _ & LAT & LAU & LAD1 & LAD2 & LR1 & LR2 & _).
      pose proof (need_new_true_full tq NN NE) as FULL.
      pose proof (batch_carved s OK lb INlb) as (CVl & _). destruct CVl as (_ & _ & _ & _ & CR5).
      split; [exact NE|].
      repeat match goal with |- _ /\ _ => split end; try assumption;
        change (class_size kBatchClass) with kBatchSize in CR5; clear - CB CR5; zlets; unfold RB, kBatchSize in *; tlia.
  Qed.
  Let LAlo : LA = 0 \/ 0x10007fff8000 <= LA.
  Proof. destruct LAF as [(_ & LA0 & _)|(_ & _ & L1 & _)]; [left; exact LA0| right; clear - L1; unfold AHI_LO in L1; tlia]. Qed.

  (* [comment removed for export] *)
  Lemma rec_vs_regc : forall x, In x (chunk_list st) ->
    (ch_end x <= RB s c + au \/ RB s c + 4294967296 <= ch_lo x \/ ch_end x <= RB s c) /\ (a_ri s + kPageSize <= ch_lo x \/ ch_end x <= a_ri s)
    /\ AIMG_TOP <= ch_lo x /\ ch_end x <= aceil.   (* [comment removed for export] *)
  Proof.
    intros x Hx. pose proof BND as B0. pose proof (record_ext s OK x Hx) as (X1 & X2 & X3 & _). pose proof (rinfo_vs_record s OK x Hx) as RI0.
    split; [| split; [exact RI0| split; [exact X1| exact X2]]].
    destruct (ch_primary x) eqn:PX.
    - pose proof (ext_facts s OK x Hx) as (_ & _ & _ & XP & _). destruct (XP PX) as (CV & EE & _).
      pose proof (carved_in_space s OK _ _ CV) as (A1 & A2 & _). destruct CV as (C1 & C2 & C3 & C4 & C5). unfold kNumClasses in C1.
      pose proof (class_size_table_facts (ch_class x) ltac:(hci; clear - C1; tlia)) as (V1 & _).
      unfold ch_lo. rewrite PX, EE.
      destruct (Z.eq_dec (ch_class x) c) as [EQ|NE].
      + rewrite EQ in *. fold st in C3, C5. fold r in C5. fold au in C5. change (region_beg st c) with (RB s c) in C3, C5. clear - C3 C5. zlets. tlia.
      + pose proof (regions_disjoint st (ch_class x) c ltac:(hci; clear - C1; tlia) ltac:(hci; clear - B0; tlia) NE) as D. change (region_beg st c) with (RB s c) in D.
        pose proof (ro_alloc_le _ _ (WF_region st (ch_class x) WFs ltac:(hci; unfold kNumClasses; clear - C1; tlia))) as AL.
        pose proof (ro_mapped_bound _ _ (WF_region st (ch_class x) WFs ltac:(hci; unfold kNumClasses; clear - C1; tlia))) as MB.
        fold st in C3, C5. unfold kUserMapSize, kFreeArrayOffset, kSpaceSize in *. clear - C3 C5 V1 D AL MB. tlia.
    - pose proof (record_vs_space s OK x Hx PX) as D. fold sb in D. pose proof (region_in_space st c ltac:(hci; clear - HC; tlia)) as [RS1 RS2].
      change (region_beg st c) with (RB s c) in RS1, RS2. change (as_space_beg st) with sb in RS1, RS2.
      unfold kSpaceSize, kPageSize in *. clear - D RS1 RS2. tlia.
  Qed.

  (* [comment removed for export] *)
  Ltac whsplit := unfold Wh, free_head_W; cbn [outside depot_W app]; repeat split; try exact I.
  (* [comment removed for export] *)
  Lemma ZH_core : forall a, a < aceil -> ~ (AIAINIT <= a < AIAINIT + 4) -> ~ (AIAINST <= a < AIAINST + 0x81030) ->
    ~ (7915480 <= a < 12109808) -> ~ (7849928 <= a < 7849956) -> ~ (U - 16 <= a < U - 12) -> ~ (U <= a < U + 8) -> ~ (TH + 2800 <= a < TH + 3169) ->
    ~ (sh U <= a < sh U + nsh size) -> ~ (d_nb d <= a < d_nb d + 16 * 65536) -> ~ (d_sb d <= a < d_sb d + 8 * 131072) -> outside Wh a.
  Proof.
    intros a Ha N1 N2 N3 N4 N5 N6 N7 N8 N9 N10. pose proof BND as B0. clear - Ha N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 B0. whsplit; unfold AIAINIT, AIAINST in *; tlia.
  Qed.
  (* [comment removed for export] *)
  Lemma ZH_lo : forall a, 65536 <= a < AIMG_TOP -> ~ (AIAINIT <= a < AIAINIT + 4) -> ~ (AIAINST <= a < AIAINST + 0x81030) ->
    ~ (7915480 <= a < 12109808) -> ~ (7849928 <= a < 7849956) -> outside Wh a.
  Proof.
    intros a Ha N1 N2 N3 N4. pose proof BND as B0. pose proof BU as B1. bands_as (BT & _).
    apply ZH_core; try assumption; clear - Ha B0 B1 BT; unfold AIMG_TOP, AHI_LO in *; acb; tlia.
  Qed.
  (* [comment removed for export] *)
  Lemma ZH_hi : forall a, (AIMG_TOP <= a < ALOWSH_LO \/ AHI_LO <= a < aceil) -> ~ (U - 16 <= a < U - 12) -> ~ (U <= a < U + 8) -> ~ (TH + 2800 <= a < TH + 3169) ->
    ~ (d_nb d <= a < d_nb d + 16 * 65536) -> ~ (d_sb d <= a < d_sb d + 8 * 131072) -> outside Wh a.
  Proof.
    intros a Ha N1 N2 N3 N4 N5. pose proof BND as B0. pose proof BU as B1.
    apply ZH_core; try assumption; clear - Ha B0 B1; unfold AIAINIT, AIAINST, AIMG_TOP, ALOWSH_LO, AHI_LO in *; acb; tlia.
  Qed.
  (* [comment removed for export] *)
  Lemma ZH_sh : forall a, ASHADOW_BASE <= a < AHI_LO -> ~ (sh U <= a < sh U + nsh size) -> outside Wh a.
  Proof.
    intros a Ha N1. pose proof BND as B0. pose proof BU as B1. bands_as (BT & _ & _ & BN & BS). ubands_as (_ & UB & _).   (* [comment removed for export] *)
    apply ZH_core; try assumption; clear - Ha B0 B1 BT BN BS UB; unfold AIAINIT, AIAINST, AHI_LO, ASHADOW_BASE in *; acb; tlia.
  Qed.
  (* [comment removed for export] *)
  Lemma ZH_thr : forall a, TH <= a < TH + 2800 -> outside Wh a.
  Proof.
    intros a Ha. pose proof BND as B0. pose proof BU as B1. pose proof BDJ as (_ & _ & _ & D1 & D2 & _ & _ & DU & _). bands_as (BT & _).
    apply ZH_core; try assumption; clear - Ha B0 B1 D1 D2 DU BT; unfold AIAINIT, AIAINST in *; zlets; acb; try tlia.
    all: unfold sh, ASHADOW_BASE in *; Z.div_mod_to_equations; tlia.
  Qed.
  Lemma ZH_rinfo : forall a, a_ri s <= a < a_ri s + kPageSize -> outside Wh a.
  Proof.
    intros a Ha. pose proof BND as (_ & _ & _ & _ & _ & _ & SB1 & SB2 & _). pose proof BDJ as (D0 & _ & _ & _ & _ & D1 & D2 & _).
    pose proof (rec_vs_regc ch CHIN) as (_ & RI0 & _). pose proof EXT as (E1 & _ & E3 & _). unfold a_ri in *.
    apply ZH_hi; [clear - Ha SB1 SB2| clear - Ha RI0 E1 E3| clear - Ha RI0 E1 E3| clear - Ha D0| clear - Ha D1| clear - Ha D2]; zfin.
  Qed.
  Lemma ZH_regc : forall a, RB s c + au <= a < RB s c + 4294967296 -> outside Wh a.
  Proof.
    intros a Ha. pose proof BND as (_ & _ & _ & _ & _ & _ & SB1 & SB2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ERB & _ & C24).
    pose proof BDJ as (D0 & _ & _ & _ & _ & D1 & D2 & _). pose proof BR as (_ & _ & _ & AU & _).
    pose proof (rec_vs_regc ch CHIN) as (RC & _). pose proof EXT as (E1 & _ & E3 & _).
    apply ZH_hi; [clear - Ha SB1 SB2 ERB C24 AU| clear - Ha RC E1 E3 AU| clear - Ha RC E1 E3 AU| clear - Ha D0 ERB C24 AU| clear - Ha D1 ERB C24 AU| clear - Ha D2 ERB C24 AU]; zfin.
  Qed.

  (* [comment removed for export] *)
  Ltac trh lem AG WM H Z B := eapply (lem _ _ _ AG WM); [exact H|];
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul Z.mul length];
    let Ha := fresh in intros ? Ha; apply Z; clear - Ha B; try acb; zfin.
  (* [comment removed for export] *)
  Lemma refill_cells_at1 : forall m1, munch Wh m m1 -> wmono asegs m m1 ->
    exists (q0 q1 q2 q3 : word),
       rw_cells asegs m1 P [C4 (wz 0); C4 (wz (if as_cache_inited st then max_count c else 0))]
    /\ stk asegs m1 (P + 16) (P + 80)
    /\ (forall c', 1 <= c' <= 31 -> exists mc cs, rw_cells asegs m1 (CA + 80 * c' + 4) [C4 mc] /\ rw_cells asegs m1 (CA + 80 * c' + 8) [C8 cs]
                                   /\ (as_cache_inited st = true -> mc = wz (max_count c') /\ cs = wz (class_size c')))
    /\ rw_cells asegs m1 (TH + 2768) [C8 q0; C8 q1; C8 q2; C8 q3]
    /\ rw_cells asegs m1 RI [C8 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz nf); C8 (wz mfa); C8 (wz au); C8 (wz 0); C8 (wz mu); C8 (wz 0)]
    /\ stk asegs m1 (RI + 64) (RI + 68) /\ rw_cells asegs m1 (RI + 68) [C1 (b8 0)] /\ stk asegs m1 (RI + 69) (RI + 128)
    /\ u32arr asegs m1 (FA s c) (wlist (rev fl))
    /\ stk asegs m1 (FA s c + 4 * nf) (FA s c + mfa)
    /\ stk asegs m1 (RB s c + au) (RB s c + mu)
    /\ rw_cells asegs m1 6976184 [C8 (wz sb); C4 (wz 0xffffffff); C4 (wz 0)] /\ rw_cells asegs m1 6976200 [C8 (wz (a_ri s))] /\ rw_cells asegs m1 6976208 [C8 (wz 0)]
    /\ rw_cells asegs m (TH + 2128) [C4 (wz 0)].
  Proof.
    intros m1 MU WM. pose proof BND as B0. pose proof BR as B2. pose proof (munch_agree _ _ _ MU) as AG.
    destruct (refill_cells_of_arep s m c R HC MISS) as (q0 & q1 & q2 & q3 & PC1 & PCJ & FAM & QST & TST & RIC & RIJ & EXH & RST & FARR & FAJ & USJ & REN).
    fold st TH in PC1, PCJ, FAM, QST, RIC, RIJ, EXH, RST, FARR, FAJ, USJ. fold r in RIC, FARR, FAJ, USJ. fold nf mfa au mu fl in RIC, FARR, FAJ, USJ.
    unfold a_cache, OT_CACHE, PCLASS_SIZE, REGIONINFO_SIZE in PC1, PCJ, FAM, RIC, RIJ, EXH, RST. fold CA in PC1, PCJ, FAM. fold P in PC1, PCJ. fold RI in RIC, RIJ, EXH, RST.
    exists q0, q1, q2, q3.
    split; [trh rw_cells_transport_pt AG WM PC1 ZH_thr B0|].
    split; [trh stk_transport_pt AG WM PCJ ZH_thr B0|].
    split. { intros c' Hc'. destruct (FAM c' Hc') as (mc & cs & V1 & V2 & V3). exists mc, cs. pose proof (conj B0 Hc') as B1.
             split; [trh rw_cells_transport_pt AG WM V1 ZH_thr B1|]. split; [trh rw_cells_transport_pt AG WM V2 ZH_thr B1| exact V3]. }
    split; [trh rw_cells_transport_pt AG WM QST ZH_thr B0|].
    split; [trh rw_cells_transport_pt AG WM RIC ZH_rinfo B0|].
    split; [trh stk_transport_pt AG WM RIJ ZH_rinfo B0|]. split; [trh rw_cells_transport_pt AG WM EXH ZH_rinfo B0|]. split; [trh stk_transport_pt AG WM RST ZH_rinfo B0|].
    pose proof (conj B0 B2) as BB.
    split; [trh u32arr_transport_pt AG WM FARR ZH_regc BB|].
    split; [trh stk_transport_pt AG WM FAJ ZH_regc BB|].
    split; [trh stk_transport_pt AG WM USJ ZH_regc BB|].
    destruct REN as [_ I1 I2 I3].
    assert (ZI : forall a, 6976184 <= a < 6976216 -> outside Wh a) by (intros a Ha; apply ZH_lo; unfold AIMG_TOP, AIAINIT, AIAINST; clear - Ha; tlia).
    split; [trh rw_cells_transport_pt AG WM I1 ZI B0|]. split; [trh rw_cells_transport_pt AG WM I2 ZI B0|]. split; [trh rw_cells_transport_pt AG WM I3 ZI B0|].
    apply (proj1 (rw_cells_app asegs _ _ [_] [_])) in PC1. destruct PC1 as [PC1 _]. replace (TH + 2128) with P by (clear - B0; tlia). exact PC1.
  Qed.

  (* [comment removed for export] *)
  Section AfterRefill.
    Variables (m1 m2 : mem) (q0 q1 q2 q3 : word).
    Hypothesis MU1 : munch Wh m m1.
    Hypothesis WM1 : wmono asegs m m1.
    Hypothesis MU2 : munch Wf m1 m2.
    Hypothesis WM2 : wmono asegs m1 m2.
    Hypothesis MI0 : mem_inv asegs m.
    Hypothesis MI2 : mem_inv asegs m2.
    (* [comment removed for export] *)
    Hypothesis PCN : rw_cells asegs m2 P [C4 (wz n)].
    Hypothesis FAM2 : forall c', 1 <= c' <= 31 -> rw_cells asegs m2 (CA + 80 * c' + 4) [C4 (wz (max_count c'))] /\ rw_cells asegs m2 (CA + 80 * c' + 8) [C8 (wz (class_size c'))].
    Hypothesis CHA : u32arr asegs m2 (P + 16) (wlist (rev (firstn (Z.to_nat n) fl1))).
    Hypothesis CHJ : stk asegs m2 (P + 16 + 4 * n) (P + 80).
    Hypothesis RI2 : rw_cells asegs m2 RI [C8 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz (nf1 - n)); C8 (wz mfa'); C8 (wz au'); C8 (wz 0); C8 (wz mu'); C8 (wz 0)].
    Hypothesis RIJ2 : stk asegs m2 (RI + 64) (RI + 68).
    Hypothesis EXH2 : rw_cells asegs m2 (RI + 68) [C1 (b8 0)].
    Hypothesis RST2 : stk asegs m2 (RI + 69) (RI + 128).
    Hypothesis FARR2 : u32arr asegs m2 (FA s c) (wlist (rev fl1)).
    Hypothesis FAJ2 : stk asegs m2 (FA s c + 4 * nf1) (FA s c + mfa').
    Hypothesis USJ2 : stk asegs m2 (RB s c + au) (RB s c + mu').
    Hypothesis POIu2 : poisoned m2 (RB s c + mu) (Z.to_nat ((mu' - mu) / 8)) 0xfa.
    Hypothesis POIf2 : poisoned m2 (FA s c + mfa) (Z.to_nat ((mfa' - mfa) / 8)) 0xfa.
    Hypothesis QST2 : rw_cells asegs m2 (TH + 2768) [C8 q0; C8 q1; C8 q2; C8 q3].
    Hypothesis TST2 : stk asegs m2 (TH + 2800) (TH + 3168).
    (* [comment removed for export] *)
    Hypothesis UNW1 : rw_cells asegs m1 (TH + 3168) [C1 (b8 0)].

    Definition free_mR : mem := chim Wo m m2.
    Let mR := free_mR.

    (* [comment removed for export] *)
    Ltac wfsplit := unfold Wf, rf_W; cbn [outside];
      repeat lazymatch goal with
        | |- _ /\ _ => split
        | |- outside (icW _) _ => apply outside_icW_far; tlia
        | |- True => exact I
        | |- ~ _ => tlia
        end.
    (* [comment removed for export] *)
    Lemma ZR_lo : forall a, 65536 <= a < AIMG_TOP -> outside Wf a.
    Proof. intros a Ha. pose proof BND as B0. pose proof BR as B1. pose proof SHB as B2. bands_as (BT & _). clear - Ha B0 B1 B2 BT. acb. unfold AIMG_TOP in *. wfsplit. Qed.
    Lemma ZR_stack : forall a, spv + -2272 <= a -> outside Wf a.
    Proof. intros a Ha. pose proof BND as B0. pose proof BR as B1. pose proof SHB as B2. pose proof HI as HI'. clear - Ha B0 B1 B2 HI'. acb. wfsplit. Qed.
    Lemma ZR_thr : forall a, TH <= a < TH + 4096 -> ~ (P <= a < P + 4) -> ~ (P + 16 <= a < P + 80) -> ~ (TH + 292 <= a < TH + 2704) -> ~ (TH + 2792 <= a < TH + 3168) -> outside Wf a.
    Proof. intros a Ha N1 N2 N3 N4. pose proof BND as B0. pose proof BR as B1. pose proof SHB as B2. pose proof BDJ as (B3 & _). bands_as (BT & _). clear - Ha N1 N2 N3 N4 B0 B1 B2 B3 BT. acb. wfsplit. Qed.
    Lemma ZR_hi : forall a, AHI_LO <= a < aceil -> ~ (TH <= a < TH + 4096) -> ~ (RI <= a < RI + 80) -> ~ (FA s c + 4 * nf <= a < FA s c + mfa') -> ~ (RB s c + mu <= a < RB s c + mu') ->
      outside Wf a.
    Proof. intros a Ha N1 N2 N3 N4. pose proof BND as B0. pose proof BR as B1. pose proof SHB as B2. clear - Ha N1 N2 N3 N4 B0 B1 B2. acb. unfold AHI_LO in *. wfsplit. Qed.
    Lemma ZR_sh : forall lo' kk a, 0 <= lo' -> lo' mod 8 = 0 -> 0 <= kk -> lo' + 8 * kk <= aceil ->
      (lo' + 8 * kk <= RB s c + mu \/ RB s c + mu' <= lo') -> (lo' + 8 * kk <= FA s c + mfa \/ FA s c + mfa' <= lo') ->
      sh lo' <= a < sh lo' + kk -> outside Wf a.
    Proof.
      intros lo' kk a H0 H8 Hk Hhi D1 D2 Ha. pose proof BND as B0. pose proof BR as B1. pose proof SHB as B2. destruct ALN as (M1 & M2 & M3 & M4 & _).
      assert (SS1 : sh lo' + kk <= sh (RB s c + mu) \/ sh (RB s c + mu) + (mu' - mu) / 8 <= sh lo') by (clear - H8 M1 M2 Hk D1 B1; apply sh_sep; try assumption; tlia).
      assert (SS2 : sh lo' + kk <= sh (FA s c + mfa) \/ sh (FA s c + mfa) + (mfa' - mfa) / 8 <= sh lo') by (clear - H8 M3 M4 Hk D2 B1; apply sh_sep; try assumption; tlia).
      assert (SB : 0x7fff8000 <= sh lo' /\ sh lo' + kk <= 0x10007fef8000) by (clear - H0 Hk Hhi; acb; unfold sh, ASHADOW_BASE; Z.div_mod_to_equations; tlia).
      bands_as (BT & _). clear - Ha B0 B1 B2 SS1 SS2 SB BT. acb. wfsplit.
    Qed.
    (* [comment removed for export] *)
    Lemma ZR_lo2 : forall a, AIMG_TOP <= a < ALOWSH_LO -> ~ (TH <= a < TH + 4096) -> outside Wf a.
    Proof. intros a Ha N1. pose proof BND as B0. pose proof BR as B1. pose proof SHB as B2. clear - Ha N1 B0 B1 B2. acb. unfold AIMG_TOP, ALOWSH_LO, AHI_LO in *. wfsplit. Qed.
    (* [comment removed for export] *)
    Lemma ZR_rec : forall a, ch_lo ch <= a < ch_end ch -> outside Wf a.
    Proof.
      intros a Ha. pose proof BND as B0. pose proof BR as B1. pose proof (rec_vs_regc ch CHIN) as (RC & RI0 & X1 & X2). pose proof (rec_vs_thread s m ch R CHIN) as RT.
      pose proof EXT as (_ & _ & _ & E4 & E5 & _). ubands_as (_ & _ & UC).
      unfold a_ri, kPageSize in *. destruct UC as [UC|UC].
      - apply ZR_lo2; clear - Ha RT E4 UC; zfin.
      - apply ZR_hi; clear - Ha B0 B1 RC RI0 X1 X2 RT E5 UC; zfin.
    Qed.
    Lemma ZR_rec_sh : forall a, sh U <= a < sh U + nsh size -> outside Wf a.
    Proof.
      intros a Ha. pose proof BND as B0. pose proof BR as B1. pose proof BU as B3. pose proof (rec_vs_regc ch CHIN) as (RC & _). pose proof EXT as (E1 & E2 & _). destruct ALN as (_ & _ & _ & _ & U8).
      apply (ZR_sh U (nsh size) a); try assumption; clear - B0 B1 B3 RC E1 E2 Ha; zfin.
    Qed.
    (* [comment removed for export] *)
    Lemma ZR_lastbatch : forall a, l <> [] -> LA <= a < LA + kBatchSize -> outside Wf a.
    Proof.
      intros a NE Ha. pose proof BND as B0. pose proof BR as B1.
      destruct LAF as [(EL & _)|(_ & _ & Q1 & Q2 & Q3 & _ & _ & _ & Q7 & Q8 & _ & _ & _ & Q9)]; [exfalso; exact (NE EL)|].
      apply ZR_hi; clear - Ha B0 B1 Q1 Q2 Q3 Q7 Q8 Q9; zfin.
    Qed.
    (* [comment removed for export] *)
    Lemma ZR_depot : depot_avoid Wf d.
    Proof.
      pose proof BND as B0. pose proof BR as B1. pose proof SHB as B2. pose proof BDJ as (_ & _ & _ & GD1 & GD2 & GD3 & GD4 & _).
      unfold depot_avoid, avoids, Wf, rf_W.
      split; [| split; [| split]].
      - bands_as (BT & _). do 13 (apply Forall_cons; [cbn [fst snd]; clear - B0 B1 B2 BT; acb; tlia|]). apply icW_avoids. clear - B0 BT; tlia.
      - bands_as (BT & _). do 13 (apply Forall_cons; [cbn [fst snd]; clear - B0 B1 B2 BT; acb; tlia|]). apply icW_avoids. clear - B0 BT; tlia.
      - bands_as (_ & _ & _ & BN & _). do 13 (apply Forall_cons; [cbn [fst snd]; clear - B0 B1 B2 GD1 GD3 BN; acb; tlia|]). apply icW_avoids. clear - B0 GD1; tlia.
      - bands_as (_ & _ & _ & _ & BS). do 13 (apply Forall_cons; [cbn [fst snd]; clear - B0 B1 B2 GD2 GD4 BS; acb; tlia|]). apply icW_avoids. clear - B0 GD2; tlia.
    Qed.

    (* [comment removed for export] *)
    Lemma MIR : mem_inv asegs mR. Proof. exact (chim_mem_inv Wo m m2 MI0 MI2). Qed.
    Lemma AGoR : agree_on (outside Wo) m2 mR. Proof. exact (chim_agree_out Wo m m2). Qed.
    Lemma AGRo : agree_on (outside Wo) mR m2. Proof. exact (agree_on_sym _ _ _ AGoR). Qed.
    Lemma WM02 : wmono asegs m m2. Proof. exact (wmono_trans _ _ _ _ WM1 WM2). Qed.
    Lemma WM0R : wmono asegs m mR. Proof. exact (chim_wmono_in Wo m m2 WM02). Qed.
    (* [comment removed for export] *)
    Lemma AG0R : agree_on (outside WR) m mR.
    Proof.
      intros x Hx Hr. unfold mR, free_mR, chim. rewrite wa_unsigned by exact Hr. destruct (inb Wo x) eqn:E; [reflexivity|].
      apply inb_false_outside in E.
      transitivity (m1 (wa x)).
      - apply MU2. rewrite wa_unsigned by exact Hr. revert Hx. unfold WR, Wf, rf_W. cbn [outside]. clear. intros (X1 & X2 & X3 & REST).
        split; [clear - X1; tlia| exact REST].
      - apply MU1. rewrite wa_unsigned by exact Hr. revert Hx E. unfold WR, Wo, Wh, free_head_W, rf_W. cbn [outside depot_W app]. clear.
        intros (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & _) (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & _).
        repeat split; try assumption. clear - X15. tlia.
    Qed.

    (* [comment removed for export] *)
    Ltac wosplit := unfold Wo; cbn [outside depot_W app]; repeat split; try exact I.
    Lemma ZWo_core : forall a, ~ (AIAINIT <= a < AIAINIT + 4) -> ~ (AIAINST <= a < AIAINST + 0x81030) -> ~ (7915480 <= a < 12109808) -> ~ (7849928 <= a < 7849956) ->
      ~ (U - 16 <= a < U - 12) -> ~ (U <= a < U + 8) -> ~ (sh U <= a < sh U + nsh size) ->
      ~ (d_nb d <= a < d_nb d + 16 * 65536) -> ~ (d_sb d <= a < d_sb d + 8 * 131072) -> outside Wo a.
    Proof. intros a N1 N2 N3 N4 N5 N6 N7 N8 N9. clear - N1 N2 N3 N4 N5 N6 N7 N8 N9. wosplit; unfold AIAINIT, AIAINST in *; tlia. Qed.
    Lemma ZWo_hi : forall a, (AIMG_TOP <= a < ALOWSH_LO \/ AHI_LO <= a < aceil) -> ~ (U - 16 <= a < U - 12) -> ~ (U <= a < U + 8) ->
      ~ (d_nb d <= a < d_nb d + 16 * 65536) -> ~ (d_sb d <= a < d_sb d + 8 * 131072) -> outside Wo a.
    Proof. intros a Ha N1 N2 N3 N4. pose proof BND as B0. pose proof BU as B1. apply ZWo_core; try assumption; clear - Ha B0 B1; unfold AIAINIT, AIAINST, AIMG_TOP, ALOWSH_LO, AHI_LO in *; acb; tlia. Qed.
    Lemma ZWo_sh : forall a, ASHADOW_BASE <= a < AHI_LO -> ~ (sh U <= a < sh U + nsh size) -> outside Wo a.
    Proof. intros a Ha N1. pose proof BND as B0. pose proof BU as B1. bands_as (_ & _ & _ & BN & BS). ubands_as (_ & UB & _). apply ZWo_core; try assumption; clear - Ha B0 B1 BN BS UB; unfold AIAINIT, AIAINST, AHI_LO, ASHADOW_BASE in *; acb; tlia. Qed.   (* [comment removed for export] *)
    Lemma ZWo_thr : forall a, TH <= a < TH + 4096 -> outside Wo a.
    Proof.
      intros a Ha. pose proof BND as B0. pose proof BU as B1. pose proof BDJ as (_ & _ & _ & D1 & D2 & _ & _ & DU & _). bands_as (BT & _).
      apply ZWo_core; clear - Ha B0 B1 D1 D2 DU BT; unfold AIAINIT, AIAINST in *; zlets; acb; try tlia.
      all: unfold sh, ASHADOW_BASE in *; Z.div_mod_to_equations; tlia.
    Qed.
    Lemma ZWo_rinfo : forall a, a_ri s <= a < a_ri s + kPageSize -> outside Wo a.
    Proof.
      intros a Ha. pose proof BND as (_ & _ & _ & _ & _ & _ & SB1 & SB2 & _). pose proof BDJ as (_ & _ & _ & _ & _ & D1 & D2 & _).
      pose proof (rec_vs_regc ch CHIN) as (_ & RI0 & _). pose proof EXT as (E1 & _ & E3 & _). unfold a_ri in *.
      apply ZWo_hi; [clear - Ha SB1 SB2| clear - Ha RI0 E1 E3| clear - Ha RI0 E1 E3| clear - Ha D1| clear - Ha D2]; zfin.
    Qed.
    Lemma ZWo_regc : forall a, RB s c + au <= a < RB s c + 4294967296 -> outside Wo a.
    Proof.
      intros a Ha. pose proof BND as (_ & _ & _ & _ & _ & _ & SB1 & SB2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ERB & _ & C24).
      pose proof BDJ as (_ & _ & _ & _ & _ & D1 & D2 & _). pose proof BR as (_ & _ & _ & AU & _).
      pose proof (rec_vs_regc ch CHIN) as (RC & _). pose proof EXT as (E1 & _ & E3 & _).
      apply ZWo_hi; [clear - Ha SB1 SB2 ERB C24 AU| clear - Ha RC E1 E3 AU| clear - Ha RC E1 E3 AU| clear - Ha D1 ERB C24 AU| clear - Ha D2 ERB C24 AU]; zfin.
    Qed.
    Lemma ZWo_SH : forall lo' kk a, 0 <= lo' -> lo' mod 8 = 0 -> 0 <= kk -> lo' + 8 * kk <= aceil ->
      (lo' + 8 * kk <= U \/ U + round_up size 8 <= lo') -> sh lo' <= a < sh lo' + kk -> outside Wo a.
    Proof.
      intros lo' kk a H0 H8 Hk Hhi Hd Ha. pose proof BU as B1. destruct ALN as (_ & _ & _ & _ & U8).
      assert (SS : sh lo' + kk <= sh U \/ sh U + nsh size <= sh lo') by (apply sh_sep; try assumption; clear - B1 Hd; tlia).
      assert (SB : 0x7fff8000 <= sh lo' /\ sh lo' + kk <= 0x10007fef8000) by (clear - H0 Hk Hhi; acb; unfold sh, ASHADOW_BASE; Z.div_mod_to_equations; tlia).
      apply ZWo_sh; [unfold ASHADOW_BASE, AHI_LO| ]; clear - Ha SS SB; tlia.
    Qed.
    Lemma ZWo_regc_sh : forall lo' kk a, RB s c + au <= lo' -> lo' + 8 * kk <= RB s c + 4294967296 -> lo' mod 8 = 0 -> 0 <= kk -> sh lo' <= a < sh lo' + kk -> outside Wo a.
    Proof.
      intros lo' kk a G1 G2 G3 G4 Ha. pose proof BND as B0. pose proof BR as B2. pose proof (rec_vs_regc ch CHIN) as (RC & _). pose proof EXT as (E1 & E2 & _).
      apply (ZWo_SH lo' kk a); try assumption; clear - G1 G2 G4 B0 B2 RC E1 E2; zfin.
    Qed.

    (* [comment removed for export] *)
    Ltac toR lem H Z B := eapply (lem (outside Wo) m2 mR AGoR); [exact H|];
      cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul Z.mul length];
      let Ha := fresh in intros ? Ha; apply Z; clear - Ha B; try acb; zfin.
    Lemma cellsR :
         rw_cells asegs mR P [C4 (wz n)]
      /\ (forall c', 1 <= c' <= 31 -> rw_cells asegs mR (CA + 80 * c' + 4) [C4 (wz (max_count c'))] /\ rw_cells asegs mR (CA + 80 * c' + 8) [C8 (wz (class_size c'))])
      /\ u32arr asegs mR (P + 16) (wlist (rev (firstn (Z.to_nat n) fl1))) /\ stk asegs mR (P + 16 + 4 * n) (P + 80)
      /\ rw_cells asegs mR RI [C8 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz (nf1 - n)); C8 (wz mfa'); C8 (wz au'); C8 (wz 0); C8 (wz mu'); C8 (wz 0)]
      /\ stk asegs mR (RI + 64) (RI + 68) /\ rw_cells asegs mR (RI + 68) [C1 (b8 0)] /\ stk asegs mR (RI + 69) (RI + 128)
      /\ u32arr asegs mR (FA s c) (wlist (rev fl1)) /\ stk asegs mR (FA s c + 4 * nf1) (FA s c + mfa')
      /\ stk asegs mR (RB s c + au) (RB s c + mu')
      /\ poisoned mR (RB s c + mu) (Z.to_nat ((mu' - mu) / 8)) 0xfa /\ poisoned mR (FA s c + mfa) (Z.to_nat ((mfa' - mfa) / 8)) 0xfa
      /\ rw_cells asegs mR (TH + 2768) [C8 q0; C8 q1; C8 q2; C8 q3] /\ stk asegs mR (TH + 2800) (TH + 3168)
      /\ rw_cells asegs mR (TH + 3168) [C1 (b8 0)].
    Proof.
      pose proof BND as B0. pose proof BR as B1. pose proof (conj B0 B1) as BB. destruct ALN as (M1 & M2 & M3 & M4 & _).
      split; [toR rw_cells_pteq PCN ZWo_thr B0|].
      split. { intros c' Hc'. destruct (FAM2 c' Hc') as [V1 V2]. pose proof (conj B0 Hc') as B2. split; [toR rw_cells_pteq V1 ZWo_thr B2| toR rw_cells_pteq V2 ZWo_thr B2]. }
      split. { eapply (u32arr_pteq (outside Wo) m2 mR AGoR); [exact CHA|]. unfold wlist. rewrite length_map, length_rev, length_firstn.
               intros a Ha. apply ZWo_thr. clear - Ha B0 B1. tlia. }
      split; [toR stk_pteq CHJ ZWo_thr BB|].
      split; [toR rw_cells_pteq RI2 ZWo_rinfo B0|].
      split; [toR stk_pteq RIJ2 ZWo_rinfo B0|]. split; [toR rw_cells_pteq EXH2 ZWo_rinfo B0|]. split; [toR stk_pteq RST2 ZWo_rinfo B0|].
      split. { eapply (u32arr_pteq (outside Wo) m2 mR AGoR); [exact FARR2|]. unfold wlist. rewrite length_map, length_rev. pose proof BR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LEN & _).
               intros a Ha. apply ZWo_regc. unfold zlen in LEN. clear - Ha B0 B1 LEN. tlia. }
      split; [toR stk_pteq FAJ2 ZWo_regc BB|].
      split; [toR stk_pteq USJ2 ZWo_regc BB|].
      split. { eapply (poisoned_pteq (outside Wo) m2 mR AGoR); [exact POIu2|]. rewrite Z2Nat.id by (clear - B1; Z.div_mod_to_equations; tlia).
               intros a Ha. apply (ZWo_regc_sh (RB s c + mu) ((mu' - mu) / 8) a); try assumption; clear - B0 B1 M2 Ha; tlia. }
      split. { eapply (poisoned_pteq (outside Wo) m2 mR AGoR); [exact POIf2|]. rewrite Z2Nat.id by (clear - B1; Z.div_mod_to_equations; tlia).
               intros a Ha. apply (ZWo_regc_sh (FA s c + mfa) ((mfa' - mfa) / 8) a); try assumption; clear - B0 B1 M4 Ha; tlia. }
      split; [toR rw_cells_pteq QST2 ZWo_thr B0|]. split; [toR stk_pteq TST2 ZWo_thr B0|].
      assert (UNW2 : rw_cells asegs m2 (TH + 3168) [C1 (b8 0)]).
      { eapply (rw_cells_transport_pt _ _ _ (munch_agree _ _ _ MU2) WM2); [exact UNW1|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat].
        intros a Ha. apply ZR_thr; clear - Ha B0; tlia. }
      toR rw_cells_pteq UNW2 ZWo_thr B0.
    Qed.

    (* [comment removed for export] *)
    Lemma R2 : AREP sR mR.
    Proof.
      destruct cellsR as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16).
      exact (arep_after_refill s m mR c L2 S2 AL' lo spv q0 q1 q2 q3 R HC MISS ROOM LO AG0R WM0R X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13 X14 X15 X16).
    Qed.
    Let OK2 : ast_ok sR. Proof. exact (proj1 R2). Qed.
    Lemma FXR : flagsx_rep m -> flagsx_rep mR.
    Proof. exact (flagsx_after_refill s m mR c lo spv R HC MISS ROOM LO AG0R WM0R). Qed.

    (* [comment removed for export] *)
    Lemma PCS2 : pc_chunks (get_pc st2 c) = cp :: tl chunks2 /\ pc_count (get_pc st2 c) = n /\ n = zlen chunks2.
    Proof.
      pose proof BR as B1. unfold st2. rewrite PCc. cbn [pc_chunks pc_count refill_pc]. fold st r. fold nf mfa au mu fl n. fold fl1. fold chunks2.
      assert (L2x : length chunks2 = Z.to_nat n) by (unfold chunks2; rewrite length_firstn; unfold zlen in B1; clear - B1; tlia).
      assert (TK0 : forall lx : list Z, length lx = Z.to_nat n -> lx = hd 0 lx :: tl lx) by (intros [|y ly] H; [exfalso; cbn in H; clear - H B1; tlia| reflexivity]).
      split; [exact (TK0 chunks2 L2x)|]. split; [reflexivity| unfold zlen; rewrite L2x; clear - B1; tlia].
    Qed.
    Let CHIN2 : In ch (chunk_list (a_st sR)). Proof. exact CHIN. Qed.
    Let CPIN : In cp (pc_chunks (get_pc st2 c)). Proof. rewrite (proj1 PCS2). left. reflexivity. Qed.
    Let CVB : carved st2 c B. Proof. exact (carved_cache st2 c cp WF2 HCK CPIN). Qed.
    Lemma B_facts : B = sb + c * 2^32 + cp * 16 /\ AHI_LO <= B /\ B + kBatchSize <= aceil /\ B mod 16 = 0 /\ 0 <= cp < 2^32
      /\ (TH + 4096 <= B \/ B + kBatchSize <= TH) /\ (B + kBatchSize <= U - 16 \/ U + 8 <= B)
      /\ (d_nb d + 16 * 65536 <= B \/ B + kBatchSize <= d_nb d) /\ (d_sb d + 8 * 131072 <= B \/ B + kBatchSize <= d_sb d)
      /\ sb <= B /\ B + kBatchSize <= sb + kSpaceSize /\ 0 < B.
    Proof.
      pose proof BND as B0. pose proof EXT as (E1 & _ & E3 & _).
      assert (EB : B = sb + c * 2^32 + cp * 16).
      { unfold B. rewrite compact_to_addr_eq. change (region_beg st2 c) with (region_beg st c). unfold sb, a_sb, st. rewrite region_beg_eq. reflexivity. }
      pose proof (carved_range st2 _ _ WF2 CVB) as (C1 & C2 & _). pose proof (carved_in_space sR OK2 _ _ CVB) as (CS1 & CS2 & _).
      pose proof CVB as (_ & _ & C3 & C4 & _).
      change (region_beg st2 c) with (region_beg st c) in C1, C2, C3, C4. unfold st in C1, C2, C3, C4. rewrite region_beg_eq in C1, C2, C3, C4.
      change (as_space_beg (a_st s)) with sb in C1, C2, C3, C4.
      change (a_sb sR) with sb in CS1, CS2. change (class_size c) with 8192 in C1, C2, C3, C4, CS1, CS2.
      pose proof (carved_vs_thread sR OK2 _ _ CVB) as BT. pose proof (carved_vs_depot sR OK2 _ _ CVB d DPL) as [BD1 BD2].
      pose proof (freech_vs_record sR OK2 ch CHIN2 c cp HCK (or_intror CPIN)) as BUx.
      change (a_thr sR) with TH in BT. change (class_size c) with 8192 in BT, BD1, BD2, BUx. change (compact_to_addr (a_st sR) c cp) with B in BUx.
      clear - B0 E1 E3 EB C1 C2 C3 C4 CS1 CS2 BT BD1 BD2 BUx. zlets. unfold a_sb, AHI_LO, kBatchSize, kSpaceSize, kPageSize, kBatchClass, kFreeArrayOffset in *.
      repeat match goal with |- _ /\ _ => split end; try tlia. all: Z.div_mod_to_equations; tlia.
    Qed.
    (* [comment removed for export] *)
    Lemma B_vs_LA : k <> 0 -> B + kBatchSize <= LA \/ LA + kBatchSize <= B.
    Proof.
      intros KNZ. destruct LAF as [(_ & _ & K0)|(NE & _ & _ & _ & _ & _ & _ & _ & _ & _ & INlb & _)]; [exfalso; exact (KNZ K0)|].
      assert (INlb2 : In lb (qc_list (as_tq (a_st sR)) ++ qc_list (as_gq (a_st sR)))) by exact INlb.
      pose proof (carved_vs_batch sR OK2 _ _ CVB lb INlb2 ltac:(hci; apply (batch_not_free sR OK2 lb c cp INlb2 HCK (or_intror CPIN)))) as BL.
      change (class_size c) with kBatchSize in BL. fold LA in BL. clear - BL. tlia.
    Qed.
    (* [comment removed for export] *)
    Lemma hit_cellsR : exists (j0 j1 j2 j3 : word),
         stk asegs m2 B (B + kBatchSize) /\ Forall (fun x => 0 <= x < 2^32) chunks2 /\ as_cache_inited st2 = true
      /\ rw_cells asegs mR (TH + 2768) [C8 j0; C8 j1; C8 j2; C8 j3].
    Proof.
      pose proof BND as B0. pose proof B_facts as (EB & A1 & A2 & A3 & A4 & BT & BUx & BD1 & BD2 & _).
      pose proof PCS2 as (P1 & P2 & P3).
      assert (HIT2 : pc_count (get_pc (a_st sR) c) <> 0) by (change (a_st sR) with st2; rewrite P2; pose proof BR as B1; clear - B1; tlia).
      pose proof (hit_cells_of_arep sR mR R2 c ltac:(hci; unfold c, kBatchClass, kNumClasses; tlia) HIT2) as HCL. cbv zeta in HCL.
      cbn [a_st a_cache a_sb a_thr] in HCL. change (a_st sR) with st2 in HCL. rewrite P1, P2 in HCL. cbn [hd] in HCL. fold TH sb in HCL. rewrite <- EB in HCL.
      destruct HCL as (j0 & j1 & j2 & j3 & _ & _ & _ & _ & QSTb & BJ & _ & _ & _ & _ & _ & CPS & _ & _ & INI).
      exists j0, j1, j2, j3. change (class_size c) with kBatchSize in BJ.
      split. { eapply (stk_pteq (outside Wo) mR m2 AGRo); [exact BJ|]. intros a Ha. apply ZWo_hi; clear - Ha B0 A1 A2 BT BUx BD1 BD2; zfin. }
      assert (TK : chunks2 = cp :: tl chunks2) by (rewrite <- P1; unfold st2; rewrite PCc; reflexivity).
      split; [rewrite TK; exact CPS|]. split; [exact INI|].
      change (a_thr sR + 208 + 2560) with (TH + 208 + 2560) in QSTb. replace (TH + 208 + 2560) with (TH + 2768) in QSTb by (clear; tlia). exact QSTb.
    Qed.

    (* [comment removed for export] *)
    Section HeadCells.
      Variables (b1 actx idv : Z) (hdq qbytes : Z).
      Hypothesis HDR1 : rw_cells asegs m1 (U + -16) [C1 (b8 3); C1 (b8 b1); C2 (wz 0); C4 (wz size); C8 (wz actx)].
      Hypothesis UW1 : rw_cells asegs m1 U [C8 (wz idv)].
      Hypothesis FLG1 : rw_cells asegs m1 AIAINIT [C1 (b8 1); C1 (b8 0); C2 (wz 0)].
      Hypothesis IA1 : ia_after m1.
      Hypothesis SHF1 : u8arr asegs m1 (sh U) (repeat (b8 kAsanHeapFreeMagic) (Z.to_nat (nsh size))).
      Hypothesis TQ1 : rw_cells asegs m1 (TH + OT_TQ) [C8 (wz k); C8 (wz hdq); C8 (wz LA); C8 (wz qbytes)].
      Hypothesis LC1 : k <> 0 -> rw_cells asegs m1 LA [C8 (wz 0)] /\ rw_cells asegs m1 (LA + 16) [C8 (wz kBatchCount)].
      Hypothesis INST0 : rw_cells asegs m (AINST + OI_SPACEBEG) [C8 (wz sb)].

      Lemma head_cells2 :
           rw_cells asegs m2 (U + -16) [C1 (b8 3); C1 (b8 b1); C2 (wz 0); C4 (wz size); C8 (wz actx)]
        /\ rw_cells asegs m2 U [C8 (wz idv)]
        /\ rw_cells asegs m2 AIAINIT [C1 (b8 1); C1 (b8 0); C2 (wz 0)] /\ ia_after m2
        /\ u8arr asegs m2 (sh U) (repeat (b8 kAsanHeapFreeMagic) (Z.to_nat (nsh size)))
        /\ rw_cells asegs m2 (TH + OT_TQ) [C8 (wz k); C8 (wz hdq); C8 (wz LA); C8 (wz qbytes)]
        /\ (k <> 0 -> rw_cells asegs m2 LA [C8 (wz 0)])
        /\ rw_cells asegs m2 (AINST + OI_SPACEBEG) [C8 (wz sb)].
      Proof.
        pose proof BND as B0. pose proof BU as B1. pose proof EXT as (E1 & E2 & E3 & _). pose proof (munch_agree _ _ _ MU2) as AG2.
        pose proof (conj E1 E3) as BE.
        split; [trh rw_cells_transport_pt AG2 WM2 HDR1 ZR_rec BE|].
        split; [trh rw_cells_transport_pt AG2 WM2 UW1 ZR_rec BE|].
        split; [unfold AIAINIT in *; trh rw_cells_transport_pt AG2 WM2 FLG1 ZR_lo B0|].
        split. { apply (ia_if_transport true Wf m1 m2 IA1 MU2 WM2). pose proof BR as B2. pose proof SHB as B3. bands_as (BT & _). clear - B0 B2 B3 BT. acb. unfold Wf, rf_W. cbn [disjoint_from].
                 repeat lazymatch goal with
                   | |- disjoint_from (icW _) _ _ => apply icW_disjoint; tlia
                   | |- _ /\ _ => split; [tlia|]
                   end. }
        split. { eapply (u8arr_pteq _ m1 m2 AG2); [exact SHF1|]. rewrite repeat_length, Z2Nat.id by (clear - B1; unfold nsh; Z.div_mod_to_equations; tlia). exact ZR_rec_sh. }
        split. { unfold OT_TQ in *. eapply (rw_cells_transport_pt _ _ _ AG2 WM2); [exact TQ1|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul Z.mul length].
                 intros a Ha. apply ZR_thr; clear - Ha B0; tlia. }
        split. { intros KNZ. destruct (LC1 KNZ) as [LC _]. assert (NE : l <> []) by (intros EL; apply KNZ; unfold k; rewrite EL; reflexivity).
                 eapply (rw_cells_transport_pt _ _ _ AG2 WM2); [exact LC|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul Z.mul length].
                 intros a Ha. apply (ZR_lastbatch a NE). unfold kBatchSize. clear - Ha. tlia. }
        unfold AINST, OI_SPACEBEG in *.
        assert (INST1 : rw_cells asegs m1 (6976152 + 32) [C8 (wz sb)]).
        { eapply (rw_cells_transport_pt _ _ _ (munch_agree _ _ _ MU1) WM1); [exact INST0|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul Z.mul length].
          intros a Ha. apply ZH_lo; unfold AIMG_TOP, AIAINIT, AIAINST; clear - Ha; tlia. }
        trh rw_cells_transport_pt AG2 WM2 INST1 ZR_lo B0.
      Qed.
    End HeadCells.

    (* [comment removed for export] *)
    Theorem after_refill_bundle : forall (b1 actx idv hdq qbytes : Z),
      rw_cells asegs m1 (U + -16) [C1 (b8 3); C1 (b8 b1); C2 (wz 0); C4 (wz size); C8 (wz actx)] ->
      rw_cells asegs m1 U [C8 (wz idv)] ->
      rw_cells asegs m1 AIAINIT [C1 (b8 1); C1 (b8 0); C2 (wz 0)] -> ia_after m1 ->
      u8arr asegs m1 (sh U) (repeat (b8 kAsanHeapFreeMagic) (Z.to_nat (nsh size))) ->
      rw_cells asegs m1 (TH + OT_TQ) [C8 (wz k); C8 (wz hdq); C8 (wz LA); C8 (wz qbytes)] ->
      (k <> 0 -> rw_cells asegs m1 LA [C8 (wz 0)] /\ rw_cells asegs m1 (LA + 16) [C8 (wz kBatchCount)]) ->
      rw_cells asegs m (AINST + OI_SPACEBEG) [C8 (wz sb)] ->
         (AREP sR mR /\ mem_inv asegs mR /\ wmono asegs m mR /\ agree_on (outside WR) m mR /\ (flagsx_rep m -> flagsx_rep mR))
      /\ (B = sb + c * 2^32 + cp * 16 /\ AHI_LO <= B /\ B + kBatchSize <= aceil /\ (TH + 4096 <= B \/ B + kBatchSize <= TH) /\ (B + kBatchSize <= U - 16 \/ U + 8 <= B)
          /\ (d_nb d + 16 * 65536 <= B \/ B + kBatchSize <= d_nb d) /\ (d_sb d + 8 * 131072 <= B \/ B + kBatchSize <= d_sb d) /\ 0 < B
          /\ (k <> 0 -> B + kBatchSize <= LA \/ LA + kBatchSize <= B))
      /\ (n = 1 /\ n = zlen chunks2 /\ chunks2 = cp :: tl chunks2 /\ Forall (fun x => 0 <= x < 2^32) chunks2)
      /\ ((l = [] /\ LA = 0 /\ k = 0)
          \/ (l <> [] /\ 1 <= k /\ AHI_LO <= LA /\ LA + kBatchSize <= aceil /\ (TH + 4096 <= LA \/ LA + kBatchSize <= TH) /\ (LA + kBatchSize <= U - 16 \/ U + 8 <= LA)
              /\ (d_nb d + 16 * 65536 <= LA \/ LA + kBatchSize <= d_nb d) /\ (d_sb d + 8 * 131072 <= LA \/ LA + kBatchSize <= d_sb d)))
      /\ stk asegs m2 B (B + kBatchSize)
      /\ rw_cells asegs m2 (U + -16) [C1 (b8 3); C1 (b8 b1); C2 (wz 0); C4 (wz size); C8 (wz actx)]
      /\ rw_cells asegs m2 U [C8 (wz idv)]
      /\ rw_cells asegs m2 AIAINIT [C1 (b8 1); C1 (b8 0); C2 (wz 0)] /\ ia_after m2
      /\ u8arr asegs m2 (sh U) (repeat (b8 kAsanHeapFreeMagic) (Z.to_nat (nsh size)))
      /\ rw_cells asegs m2 (TH + OT_TQ) [C8 (wz k); C8 (wz hdq); C8 (wz LA); C8 (wz qbytes)]
      /\ (k <> 0 -> rw_cells asegs m2 LA [C8 (wz 0)])
      /\ rw_cells asegs m2 (AINST + OI_SPACEBEG) [C8 (wz sb)]
      /\ rw_cells asegs m2 (TH + 2128) [C4 (wz n)] /\ rw_cells asegs m2 (TH + 2136) [C8 (wz kBatchSize)]
      /\ u32arr asegs m2 (TH + 2144) (wlist (rev chunks2)) /\ stk asegs m2 (TH + 2144 + 4 * n) (TH + 2208)
      /\ rw_cells asegs m2 (TH + 3168) [C1 (b8 0)].
    Proof.
      intros b1 actx idv hdq qbytes HDR1 UW1 FLG1 IA1 SHF1 TQ1 LC1 INST0.
      pose proof BND as B0.
      destruct (head_cells2 b1 actx idv hdq qbytes HDR1 UW1 FLG1 IA1 SHF1 TQ1 LC1 INST0) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8).
      destruct hit_cellsR as (j0 & j1 & j2 & j3 & BJ & CPS & INI & _).
      pose proof B_facts as (EB & A1 & A2 & A3 & A4 & BT & BUx & BD1 & BD2 & SB1 & SB2 & BPOS).
      pose proof PCS2 as (P1 & P2 & P3).
      assert (TK : chunks2 = cp :: tl chunks2) by (rewrite <- P1; unfold st2; rewrite PCc; reflexivity).
      split. { split; [exact R2|]. split; [exact MIR|]. split; [exact WM0R|]. split; [exact AG0R| exact FXR]. }
      split. { split; [exact EB|]. split; [exact A1|]. split; [exact A2|]. split; [exact BT|]. split; [exact BUx|]. split; [exact BD1|]. split; [exact BD2|].
               split; [exact BPOS| exact B_vs_LA]. }
      split. { split; [exact NR|]. split; [exact P3|]. split; [exact TK| exact CPS]. }
      split. { destruct LAF as [L0|(Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & _)]; [left; exact L0| right]. repeat match goal with |- _ /\ _ => split end; assumption. }
      split; [exact BJ|]. split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|]. split; [exact X5|]. split; [exact X6|]. split; [exact X7|].
      split; [exact X8|].
      split; [replace (TH + 2128) with P by (clear - B0; tlia); exact PCN|].
      split. { destruct (FAM2 c ltac:(clear - HC; unfold c, kBatchClass in *; tlia)) as [_ V2]. replace (TH + 2136) with (CA + 80 * c + 8) by (clear - B0; tlia).
               change kBatchSize with (class_size c). exact V2. }
      split; [replace (TH + 2144) with (P + 16) by (clear - B0; tlia); exact CHA|].
      split; [replace (TH + 2144) with (P + 16) by (clear - B0; tlia); replace (TH + 2208) with (P + 80) by (clear - B0; tlia); exact CHJ|].
      eapply (rw_cells_transport_pt _ _ _ (munch_agree _ _ _ MU2) WM2); [exact UNW1|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat].
      intros a Ha. apply ZR_thr; clear - Ha B0; tlia.
    Qed.

    (* [comment removed for export] *)
    Section AfterTail.
      Variable m3 : mem.
      Hypothesis MU3 : munch Wn m2 m3.
      Hypothesis WM3 : wmono asegs m2 m3.

      Lemma AGR3 : agree_on (outside (Wh ++ Wn)) mR m3.
      Proof.
        intros x Hx Hr. apply outside_app in Hx. destruct Hx as [Hh Hn]. unfold mR, free_mR, chim. rewrite wa_unsigned by exact Hr.
        destruct (inb Wo x) eqn:E.
        - exfalso. apply inb_true_not_outside in E. apply E. revert Hh. unfold Wh, Wo, free_head_W. cbn [outside app]. clear. tauto.
        - pose proof (MU3 (wa x)) as M. rewrite wa_unsigned in M by exact Hr. exact (M Hn).
      Qed.
      Lemma WMR3 : wmono asegs m m3 -> wmono asegs mR m3.
      Proof. intros W03. exact (chim_wmono_out Wo m m2 m3 W03 WM3). Qed.
      (* [comment removed for export] *)
      Lemma BLKR : rw_cells asegs mR U [CB (Z.to_nat size) bs].
      Proof.
        pose proof BU as B1. pose proof EXT as (E1 & E2 & E3 & _).
        assert (AGb : agree_on (fun a => U <= a < U + size) m mR).
        { intros x Hx Hr. unfold mR, free_mR, chim. rewrite wa_unsigned by exact Hr. destruct (inb Wo x) eqn:E; [reflexivity|].
          apply inb_false_outside in E.
          assert (X8 : U + 8 <= x). { revert E Hx. unfold Wo. cbn [outside app]. clear. intros (_ & _ & _ & N4 & _) Hx. tlia. }
          ubands_as (_ & _ & UC). pose proof EXT as (_ & _ & _ & E4' & E5' & _).   (* [comment removed for export] *)
          assert (XR : ch_lo ch + 16 <= x /\ x + 1 <= ch_end ch /\ (AIMG_TOP <= x < ALOWSH_LO \/ AHI_LO <= x < aceil)) by (clear - Hx X8 E1 E2 E4' E5' B1 UC; zfin).
          transitivity (m1 (wa x)).
          - apply MU2. rewrite wa_unsigned by exact Hr. apply ZR_rec. clear - XR. tlia.
          - apply MU1. rewrite wa_unsigned by exact Hr. pose proof (rec_vs_thread s m ch R CHIN) as RT. pose proof (rec_vs_depot s m ch d R CHIN DPL) as [RD1 RD2].
            apply ZH_hi; clear - XR X8 RT RD1 RD2; zfin. }
        eapply (rw_cells_pteq _ m mR AGb); [exact BLK|]. cbn [cells_size csize Nat.add]. intros a Ha. clear - Ha B1. tlia.
      Qed.

      (* [comment removed for export] *)
      Lemma ZN_core : forall a, a < aceil -> ~ (TH + 2128 <= a < TH + 2132) -> ~ (TH + 2784 <= a < TH + 2792) -> ~ (B <= a < B + 32) ->
        ~ (TH + 80 <= a < TH + 112) -> ~ (LA <= a < LA + 8) -> outside Wn a.
      Proof.
        intros a Ha N1 N2 N3 N4 N5. pose proof BND as (A0 & _). clear - Ha N1 N2 N3 N4 N5 A0.
        unfold Wn, enq_new_W. cbn [outside]. zlets. repeat split; try exact I; tlia.
      Qed.
      (* [comment removed for export] *)
      Lemma ZN_hi : forall a, (AIMG_TOP <= a < ALOWSH_LO \/ AHI_LO <= a < aceil) -> ~ (TH <= a < TH + 2800) -> ~ (B <= a < B + 32) -> ~ (LA <= a < LA + 8) -> outside Wn a.
      Proof. intros a Ha N1 N2 N3. apply ZN_core; try assumption; clear - Ha N1; acb; unfold AIMG_TOP, ALOWSH_LO, AHI_LO in *; tlia. Qed.
      (* [comment removed for export] *)
      Lemma ZN_lo : forall a, (65536 <= a < AIMG_TOP \/ ASHADOW_BASE <= a < AHI_LO) -> outside Wn a.
      Proof.
        intros a Ha. pose proof BND as (A0 & T1 & T2 & _). pose proof LAlo as LAX. pose proof B_facts as (_ & A1 & _). bands_as (BTH & _).
        apply ZN_core; clear - Ha A0 T1 T2 LAX A1 BTH; zlets; acb; unfold AHI_LO, AIMG_TOP, ASHADOW_BASE in *; tlia.
      Qed.
      (* [comment removed for export] *)
      Lemma head_cells3 : forall (b1 actx idv : Z),
        rw_cells asegs m2 (U + -16) [C1 (b8 3); C1 (b8 b1); C2 (wz 0); C4 (wz size); C8 (wz actx)] ->
        rw_cells asegs m2 U [C8 (wz idv)] ->
        rw_cells asegs m2 AIAINIT [C1 (b8 1); C1 (b8 0); C2 (wz 0)] -> ia_after m2 ->
        u8arr asegs m2 (sh U) (repeat (b8 kAsanHeapFreeMagic) (Z.to_nat (nsh size))) ->
        rw_cells asegs m2 (TH + 3168) [C1 (b8 0)] ->
           rw_cells asegs m3 (U + -16) [C1 (b8 3); C1 (b8 b1); C2 (wz 0); C4 (wz size); C8 (wz actx)]
        /\ rw_cells asegs m3 U [C8 (wz idv)]
        /\ rw_cells asegs m3 AIAINIT [C1 (b8 1); C1 (b8 0); C2 (wz 0)] /\ ia_after m3
        /\ u8arr asegs m3 (sh U) (repeat (b8 kAsanHeapFreeMagic) (Z.to_nat (nsh size)))
        /\ stk asegs m3 (TH + 2800) (TH + 3168)
        /\ rw_cells asegs m3 (TH + 3168) [C1 (b8 0)]
        /\ depot_avoid Wn d.
      Proof.
        intros b1 actx idv HDR2 UW2 FLG2 IA2 SHF2 UNW2. pose proof (munch_agree _ _ _ MU3) as AG3.
        pose proof BND as B0. pose proof BU as B1. pose proof BDJ as (_ & _ & _ & D1 & D2 & _ & _ & DU & _).
        pose proof B_facts as (_ & A1 & A2 & _ & _ & BT & BUx & BD1 & BD2 & _). pose proof LAF as LAX.
        assert (ZU : forall a, U - 16 <= a < U + 8 -> outside Wn a).
        { intros a Ha. ubands_as (_ & UB & _). apply ZN_hi; [clear - Ha B1 UB; zfin| clear - Ha DU; zfin| clear - Ha BUx; zfin|].   (* [comment removed for export] *)
          destruct LAX as [(_ & LA0 & _)|(_ & _ & L1 & _ & _ & LU & _)]; [clear - Ha LA0 B1| clear - Ha L1 LU]; zfin. }
        split; [trh rw_cells_transport_pt AG3 WM3 HDR2 ZU B0|].
        split; [trh rw_cells_transport_pt AG3 WM3 UW2 ZU B0|].
        assert (ZS : forall a, 65536 <= a < 12599296 -> outside Wn a) by (intros a Ha; apply ZN_lo; left; unfold AIMG_TOP in *; clear - Ha; tlia).
        split; [unfold AIAINIT in *; trh rw_cells_transport_pt AG3 WM3 FLG2 ZS B0|].
        split. { apply (ia_if_transport true Wn m2 m3 IA2 MU3 WM3). pose proof LAlo as LL. pose proof BND as (A0 & T1 & _). bands_as (BTH & _). clear - A0 T1 A1 LL BTH. acb.
                 unfold Wn, enq_new_W. cbn [disjoint_from]. zlets. unfold AHI_LO in *. repeat split; tlia. }
        split. { eapply (u8arr_pteq _ m2 m3 AG3); [exact SHF2|]. rewrite repeat_length, Z2Nat.id by (clear - B1; unfold nsh; Z.div_mod_to_equations; tlia).
                 intros a Ha. apply ZN_lo. right. clear - Ha B1. unfold AHI_LO, ASHADOW_BASE. tlia. }
        assert (ZT : forall a, TH + 2800 <= a < TH + 3169 -> outside Wn a).
        { intros a Ha. pose proof BND as (_ & T1 & T2 & _). apply ZN_core; [clear - Ha T1 T2; zfin| clear - Ha; zfin| clear - Ha; zfin| clear - Ha BT; zfin| clear - Ha; zfin|].
          destruct LAX as [(_ & LA0 & _)|(_ & _ & L1 & _ & LT & _)]; [clear - Ha LA0 T1| clear - Ha L1 LT]; zfin. }
        split; [trh stk_transport_pt AG3 WM3 TST2 ZT B0|].
        split; [trh rw_cells_transport_pt AG3 WM3 UNW2 ZT B0|].
        assert (DF : aceil <= lo /\ 4096 <= TH /\ (TH + 4096 <= d_nb d \/ d_nb d + 1048576 <= TH) /\ (TH + 4096 <= d_sb d \/ d_sb d + 1048576 <= TH)
                     /\ 12599296 <= d_nb d /\ d_nb d + 16 * 65536 <= aceil /\ 12599296 <= d_sb d /\ d_sb d + 8 * 131072 <= aceil
                     /\ (TH + 4096 <= 65536 \/ (12599296 <= TH /\ TH + 4096 <= 2147446784) \/ 17594333495296 <= TH)
                     /\ 0x10007fff8000 <= B /\ (d_nb d + 16 * 65536 <= B \/ B + 8192 <= d_nb d) /\ (d_sb d + 8 * 131072 <= B \/ B + 8192 <= d_sb d)
                     /\ (LA = 0 \/ (0x10007fff8000 <= LA /\ (d_nb d + 16 * 65536 <= LA \/ LA + 8192 <= d_nb d) /\ (d_sb d + 8 * 131072 <= LA \/ LA + 8192 <= d_sb d)))).
        { pose proof BND as (A0 & T1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & G1 & G2 & G3 & G4 & _).
          bands_as (BTH & _).
          repeat match goal with |- _ /\ _ => split end; try assumption; try (clear - A1; unfold AHI_LO in A1; tlia); try (clear - BD1; unfold kBatchSize in BD1; tlia);
            try (clear - BD2; unfold kBatchSize in BD2; tlia).
          destruct LAX as [(_ & LA0 & _)|(_ & _ & L1 & _ & _ & _ & LD1 & LD2 & _)]; [left; exact LA0| right]. clear - L1 LD1 LD2. unfold AHI_LO, kBatchSize in *. repeat split; tlia. }
        clear - DF. unfold depot_avoid, avoids, Wn, enq_new_W. zlets.
        repeat match goal with |- _ /\ _ => split end; repeat (apply Forall_cons; [cbn [fst snd]; tlia|]); apply Forall_nil.
      Qed.
      (* [comment removed for export] *)
      Lemma win3 : forall (SS : list (word * word)) (x : word),
        in_rangesb x ((if mfa <? mfa' then [(wz (sh (FA s c + mfa)), wz ((mfa' - mfa) / 8))] else [])
                      ++ (if mu <? mu' then [(wz (sh (RB s c + mu)), wz ((mu' - mu) / 8))] else []) ++ SS) = true ->
        (in_rangesb x SS = true -> wview asegs m3 x <> None) -> wview asegs m3 x <> None.
      Proof.
        intros SS x Hx OLD. pose proof SHB as B2. pose proof BR as B3. rewrite !in_rangesb_app in Hx.
        apply Bool.orb_true_iff in Hx. destruct Hx as [Hx|Hx]; [| apply Bool.orb_true_iff in Hx; destruct Hx as [Hx|Hx]; [| exact (OLD Hx)]].
        - apply in_rangesb_if in Hx.
          apply in_window1 in Hx; [| clear - B2; acb; tlia| clear - B3; Z.div_mod_to_equations; tlia| clear - B2 B3; acb; Z.div_mod_to_equations; tlia].
          apply (poisoned_visible m2 m3 _ _ _ x POIf2 WM3). rewrite Z2Nat.id by (clear - B3; Z.div_mod_to_equations; tlia). exact Hx.
        - apply in_rangesb_if in Hx.
          apply in_window1 in Hx; [| clear - B2; acb; tlia| clear - B3; Z.div_mod_to_equations; tlia| clear - B2 B3; acb; Z.div_mod_to_equations; tlia].
          apply (poisoned_visible m2 m3 _ _ _ x POIu2 WM3). rewrite Z2Nat.id by (clear - B3; Z.div_mod_to_equations; tlia). exact Hx.
      Qed.
      (* [comment removed for export] *)
      Ltac trz AG WM H ZT := eapply (rw_cells_transport_pt _ _ _ AG WM); [exact H|];
        cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul Z.mul length];
        let Ha := fresh in intros ? Ha; apply ZT; clear - Ha; tlia.
      Lemma flagsx3 : wmono asegs m m3 -> flagsx_rep mR -> flagsx_rep m3.
      Proof.
        intros W03 FX. pose proof (WMR3 W03) as WMR.
        assert (ZT : forall a, 65536 <= a < AIMG_TOP -> ~ (AIAINIT <= a < AIAINIT + 4) -> ~ (AIAINST <= a < AIAINST + 0x81030) ->
                     ~ (7915480 <= a < 12109808) -> ~ (7849928 <= a < 7849956) -> outside (Wh ++ Wn) a).
        { intros a Ha N1 N2 N3 N4. apply outside_app. split; [apply ZH_lo; [clear - Ha; tlia| assumption| assumption| assumption| assumption]|].
          apply ZN_lo. left. clear - Ha. tlia. }
        destruct FX as (FXa & FXb & [g FXc] & FXd & [bb FXe]). unfold flagsx_rep, ALIBCPGSZ, AGOT_SSP, ASSPGUARD, ACFLAGS, AIAINIT, AIAINST, AIMG_TOP in *.
        split; [trz AGR3 WMR FXa ZT|]. split; [trz AGR3 WMR FXb ZT|]. split; [exists g; trz AGR3 WMR FXc ZT|]. split; [trz AGR3 WMR FXd ZT|]. exists bb; trz AGR3 WMR FXe ZT.
      Qed.

      (* [comment removed for export] *)
      Variables (LB : list (Z * Z)) (b1 actx idv : Z) (j0 j1 j2 j3 : word).
      Hypothesis ND : List.NoDup LB.
      Hypothesis LBs : forall b, In b LB <-> In b (alb s).
      Hypothesis B1 : 0 <= b1 < 256 /\ (b1 mod 128 = 17 \/ b1 mod 128 = 65).
      Hypothesis HDR3 : rw_cells asegs m3 (U + -16) [C1 (b8 3); C1 (b8 b1); C2 (wz 0); C4 (wz size); C8 (wz actx)].
      Hypothesis UW3 : rw_cells asegs m3 U [C8 (wz idv)].
      Hypothesis TST3 : stk asegs m3 (TH + 2800) (TH + 3168).
      Hypothesis UNW3 : rw_cells asegs m3 (TH + 3168) [C1 (b8 0)].
      Hypothesis FLG3 : rw_cells asegs m3 AIAINIT [C1 (b8 1); C1 (b8 0); C2 (wz 0)].
      Hypothesis IA3 : ia_after m3.
      Hypothesis SHF3 : u8arr asegs m3 (sh U) (repeat (b8 kAsanHeapFreeMagic) (Z.to_nat (nsh size))).
      Hypothesis TQ3 : rw_cells asegs m3 (TH + OT_TQ) [C8 (wz (k + 1)); C8 (wz (if k =? 0 then B else hd 0 (map qb_addr l))); C8 (wz B); C8 (wz (qc_bytes tq + (size + kBatchSize)))].
      Hypothesis LA3 : k <> 0 -> rw_cells asegs m3 LA [C8 (wz B)].
      Hypothesis NB3 : rw_cells asegs m3 B [C8 (wz 0); C8 (wz (size + kBatchSize)); C8 (wz 1); C8 (wz (U + -16))].
      Hypothesis NBJ3 : stk asegs m3 (B + 32) (B + kBatchSize).
      Hypothesis PC13 : rw_cells asegs m3 (TH + 2128) [C4 (wz (n - 1))].
      Hypothesis PC33 : u32arr asegs m3 (TH + 2144) (wlist (rev (tl chunks2))).
      Hypothesis PC43 : stk asegs m3 (TH + 2144 + 4 * (n - 1)) (TH + 2208).
      Hypothesis STATS3 : rw_cells asegs m3 (TH + 2768) [C8 j0; C8 j1; C8 j2; C8 j3].
      Hypothesis WM03 : wmono asegs m m3.

      Theorem arepq_after_refill_new : AREPQ sF [] [] m3.
      Proof.
        pose proof PCS2 as (P1 & P2 & P3).
        assert (W0 : WF (set_internal_init st2)) by (eapply WF_ext; [ .. | exact WF2]; reflexivity).
        pose proof (WFQ_free_new (set_internal_init st2) ch W0 CHIN ALLOC cp (tl chunks2) P1) as WQ'.
        assert (WQ'' : WFQ (free_st' sR ch tq' cache') [] []).
        { unfold free_new_state in WQ'. change (get_pc (set_internal_init st2) kBatchClass) with (get_pc st2 c) in WQ'. rewrite P2 in WQ'. exact WQ'. }
        pose proof (arepq_after_new sR mR m3 d lo spv ch bs cp (tl chunks2) L2 S2 AL' b1 actx idv j0 j1 j2 j3
                      R2 CHIN2 ALLOC UHI DPL LO P1 BLKR AGR3 (WMR3 WM03) B1 HDR3 UW3 TST3 UNW3 FLG3 IA3 SHF3) as AH.
        cbn [a_st a_thr a_ctx a_fsb a_L a_S a_Zr a_AL a_top a_bot] in AH. rewrite P2 in AH.
        exact (AH TQ3 LA3 NB3 NBJ3 PC13 PC33 PC43 STATS3 WQ'').
      Qed.
      Theorem arheap_after_refill_new : ARHEAP sF (lb_remove U LB) m3.
      Proof.
        pose proof PCS2 as (P1 & P2 & P3).
        assert (W0 : WF (set_internal_init st2)) by (eapply WF_ext; [ .. | exact WF2]; reflexivity).
        assert (NOD2 : qc_bytes (as_tq (set_internal_init st2)) + size + kBatchSize <= as_qcache (set_internal_init st2)).
        { change (as_tq (set_internal_init st2)) with tq. change (as_qcache (set_internal_init st2)) with (as_qcache st).
          pose proof PURE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Q3 & _). rewrite Q3. exact NOD. }
        pose proof (WF_free_new (set_internal_init st2) ch W0 CHIN ALLOC cp (tl chunks2) P1 NOD2) as WF'.
        assert (WF'' : WF (free_st' sR ch tq' cache')).
        { unfold free_new_state in WF'. change (get_pc (set_internal_init st2) kBatchClass) with (get_pc st2 c) in WF'. rewrite P2 in WF'. exact WF'. }
        pose proof (WFQ_free_new (set_internal_init st2) ch W0 CHIN ALLOC cp (tl chunks2) P1) as WQ'.
        assert (WQ'' : WFQ (free_st' sR ch tq' cache') [] []).
        { unfold free_new_state in WQ'. change (get_pc (set_internal_init st2) kBatchClass) with (get_pc st2 c) in WQ'. rewrite P2 in WQ'. exact WQ'. }
        assert (LBs2 : forall b, In b LB <-> In b (alb sR)) by exact LBs.
        pose proof (arheap_after_new sR mR m3 d lo spv ch bs cp (tl chunks2) L2 S2 AL' b1 actx idv j0 j1 j2 j3
                      R2 CHIN2 ALLOC UHI DPL LO P1 BLKR AGR3 (WMR3 WM03) B1 HDR3 UW3 TST3 UNW3 FLG3 IA3 SHF3) as AH.
        cbn [a_st a_thr a_ctx a_fsb a_L a_S a_Zr a_AL a_top a_bot] in AH. rewrite P2 in AH.
        exact (AH TQ3 LA3 NB3 NBJ3 PC13 PC33 PC43 STATS3 WQ'' LB WF'' ND LBs2).
      Qed.
      (* [comment removed for export] *)
      Lemma alb_after_refill_new : forall b, In b (lb_remove U LB) <-> In b (alb sF).
      Proof.
        intros b. rewrite lb_remove_In, LBs. pose proof PCS2 as (P1 & P2 & P3).
        unfold alb. change (a_st sF) with (free_st' sR ch tq' cache'). rewrite !in_map_iff. split.
        - intros ((x & E & Hx) & NEU). apply filter_In in Hx. destruct Hx as [Hx AX]. exists x. split; [exact E|]. apply filter_In. split; [| exact AX].
          apply (free_old_in sR ch mR tq' cache' R2 CHIN2 x Hx). intros ->. apply NEU. rewrite <- E. reflexivity.
        - intros (x & E & Hx). apply filter_In in Hx. destruct Hx as [Hx AX]. apply (free_cl sR ch mR tq' cache' R2 CHIN2) in Hx.
          destruct Hx as [->|[Hx NEU]]; [cbn in AX; discriminate AX|].
          split; [exists x; split; [exact E| apply filter_In; split; [exact Hx| exact AX]]|]. rewrite <- E. cbn [fst]. exact NEU.
      Qed.
    End AfterTail.
  End AfterRefill.
End FreeRefillFacts.
