(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FMapPositive.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import AsanAllocModel. From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both Require Import AsanAllocCons. From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import SReach LazyRestrict LazyLedger LazySR LazyNodes.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AllocWf AllocKit AllocBudget AllocRep AllocRepFacts AllocRepFacts2 AllocRepX
     AsDepotInv AW_DepotFrame AllocWalkKit AG_MallocModel AG_WFHit AG_Malloc AG_Malloc2 AG_Frame AG_RepQ AG_WriteSet AG_RecycleDefs SecLazy AllocTacX.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac lia ::=
  dle_wrap ltac:(first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ]).

Section HCW.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
Lemma awrit_dput : forall s s' d h n lo SP a, awrit s s' (d_put d h n) lo SP a <-> awrit s s' d lo SP a.
Proof. intros. unfold awrit. rewrite d_nb_put, d_sb_put. tauto. Qed.
Lemma acompl_dput : forall s s' d h n lo SP m m', acompl s s' (d_put d h n) lo SP m m' <-> acompl s s' d lo SP m m'.
Proof.
  intros s s' d h n lo SP m m'. unfold acompl. split; intros H a Ha NW; apply (H a Ha); intros W; apply NW.
  - exact (proj1 (awrit_dput s s' d h n lo SP a) W).
  - exact (proj2 (awrit_dput s s' d h n lo SP a) W).
Qed.

(* [comment removed for export] *)
Lemma awrit_zones : forall s1 s s2 d lo SP a,
  a_thr s1 = a_thr s -> a_sb s1 = a_sb s -> a_pa s1 = a_pa s -> as_sec (a_st s1) = as_sec (a_st s) ->
  awrit s1 s2 d lo SP a <-> awrit s s2 d lo SP a.
Proof. intros s1 s s2 d lo SP a Et Es Ep Ec. unfold awrit. rewrite Et, Es, Ep, Ec. tauto. Qed.

Section ComplFrame.
  Variables (s s1 s2 : ast) (LB : list (Z * Z)) (d : depot) (lo SP : Z) (m1 m2 : mem).
  Hypothesis OK : ast_ok s.
  Hypothesis HLB1 : forall b, In b LB -> In b (alb s1).
  Hypothesis E1 : a_thr s1 = a_thr s /\ a_sb s1 = a_sb s /\ a_pa s1 = a_pa s.
  Hypothesis ES : as_sec (a_st s1) = as_sec (a_st s).
  Hypothesis SUB : forall sc, In sc (as_sec (a_st s2)) -> In sc (as_sec (a_st s1)).
  Hypothesis DPL : depot_placed s d.
  Hypothesis DFS : disj (a_fsb s) AFS_SIZE (d_nb d) (16 * 65536) /\ disj (a_fsb s) AFS_SIZE (d_sb d) (8 * 131072).
  Hypothesis LO : aceil <= lo.
  Hypothesis LS : lo <= SP.

  Let NIL : forall b : Z * Z, In b [] -> In b (alb s). Proof. intros b []. Qed.

  (* [comment removed for export] *)
  Lemma client_not_awrit : forall a, aclient s [] SP a -> ~ awrit s1 s2 d lo SP a.
  Proof.
    intros a CL W. destruct E1 as (Et & Es & Ep). unfold awrit in W. rewrite Et, Es, Ep in W.
    pose proof (proj1 OK) as PL.
    pose proof PL as (Y1 & Y2 & Y3 & P1 & P2 & P3 & T1 & T2 & T3 & X1 & X2 & X3 & D1 & D2 & D3 & D4 & D5 & F1 & F2 & D6 & D7 & D8 & D9 & SEC & SEC2 & TCX).
    pose proof DPL as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
    assert (SPc : aceil <= SP) by (clear - LO LS; lia).
    destruct W as [W|[W|[W|[W|[W|[W|[W|W]]]]]]].
    - exact (apriv_stack s OK [] NIL lo SP LO a W CL).
    - refine (apriv_thread s OK [] NIL SP (a_thr s + 64) (a_thr s + kPageSize) _ _ _ SPc a W CL); unfold kPageSize; clear; lia.
    - (* [comment removed for export] *)
      refine (apriv_app s OK [] NIL SP (a_sb s) (a_sb s + kSpaceSize + kPageSize) _ _ _ _ a W CL).
      + apply arng_hi; [exact Y2| exact Y3].
      + clear - Y3 SPc. lia.
      + intros A n [].
      + clear - D6. unfold disj in D6. lia.
    - (* [comment removed for export] *)
      assert (S8 : a_sb s mod 8 = 0) by (clear - Y1; Z.div_mod_to_equations; lia).
      rewrite <- (sh_diff8 (a_sb s) (a_sb s + kSpaceSize + kPageSize) S8) in W.
      refine (apriv_shadow s OK [] NIL SP (a_sb s) (a_sb s + kSpaceSize + kPageSize) _ _ S8 SPc _ _ a W CL).
      + apply arng_hi; [exact Y2| exact Y3].
      + unfold kSpaceSize, kPageSize. clear. lia.
      + intros A n [].
      + clear - D6. unfold disj in D6. lia.
    - refine (apriv_ptrarr s OK [] NIL SP (a_pa s) (a_pa s + kPtrArrayReserve) _ _ _ SPc a W CL); unfold kPtrArrayReserve; clear; lia.
    - (* [comment removed for export] *)
      destruct W as (sc & IN & R).
      assert (INs : In sc (as_sec (a_st s))) by (destruct IN as [I|I]; [rewrite <- ES; exact I| rewrite <- ES; exact (SUB sc I)]).
      pose proof (SEC sc INs) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
      destruct R as [R|R].
      + refine (apriv_app s OK [] NIL SP (sc_map_beg sc) (sc_map_beg sc + sc_map_size sc) (arng_of_aapp _ _ Q2) _ _ _ a R CL).
        * clear - Q3 SPc. lia.
        * intros A n [].
        * clear - Q9. unfold disj in Q9. lia.
      + assert (M8 : sc_map_beg sc mod 8 = 0) by (clear - Q1; unfold kPageSize in Q1; Z.div_mod_to_equations; lia).
        replace (sc_map_size sc / 8) with ((sc_map_beg sc + sc_map_size sc - sc_map_beg sc) / 8) in R by (f_equal; clear; lia).
        refine (apriv_shadow s OK [] NIL SP (sc_map_beg sc) (sc_map_beg sc + sc_map_size sc) (arng_of_aapp _ _ Q2) _ M8 SPc _ _ a R CL).
        * clear - Q4. unfold kPageSize in Q4. lia.
        * intros A n [].
        * clear - Q9. unfold disj in Q9. lia.
    - (* [comment removed for export] *)
      unfold astatw in W. destruct W as [W|[W|[W|W]]].
      + refine (apriv_inst s OK [] NIL SP (AINST + 112) (AINST + 920) _ _ SPc a W CL); clear; lia.
      + refine (apriv_static s OK [] NIL SP 0x77c7c8 0xb8c7f0 _ SPc _ a W CL); [unfold AIMG_TOP; clear; lia| clear; lia].
      + refine (apriv_static s OK [] NIL SP AIAINIT (AIAINIT + 4) _ SPc _ a W CL); unfold AIAINIT, AIMG_TOP; clear; lia.
      + refine (apriv_static s OK [] NIL SP AIAINST (AIAINST + 0x81030) _ SPc _ a W CL); unfold AIAINST, AIMG_TOP; clear; lia.
    - (* [comment removed for export] *)
      destruct (apriv_depot_blocks s OK [] NIL SP (d_nb d) (d_sb d) G10 G12 G3 G4 G9 (proj1 DFS) (proj2 DFS) SPc) as [AN AS].
      destruct W as [W|W]; [exact (AN a W CL)| exact (AS a W CL)].
  Qed.

  (* [comment removed for export] *)
  Lemma amframe_of_compl : acompl s1 s2 d lo SP m1 m2 -> agree_on (alive (a_st s1)) m1 m2 -> amframe s LB SP m1 m2.
  Proof.
    intros AC AG a Ha CL.
    assert (D : (exists A n, In (A, n) LB /\ (A <= a < A + n \/ sh A <= a < sh A + nsh n)) \/ aclient s [] SP a).
    { unfold aclient in CL |- *. destruct CL as [C|[C|[(A & n & Hin & C)|[(A & n & Hin & C)|C]]]].
      - right. left. exact C.
      - right. right. left. exact C.
      - left. exists A, n. split; [exact Hin| left; exact C].
      - left. exists A, n. split; [exact Hin| right; exact C].
      - right. do 4 right. exact C. }
    destruct D as [(A & n & Hin & R)|C0].
    - apply (AG a); [| exact Ha]. destruct (alb_In s1 A n (HLB1 _ Hin)) as (ch & IN & AL & <- & <-).
      exists ch. split; [exact IN|]. split; [exact AL| exact R].
    - exact (AC a Ha (client_not_awrit a C0)).
  Qed.
End ComplFrame.
End HCW.
