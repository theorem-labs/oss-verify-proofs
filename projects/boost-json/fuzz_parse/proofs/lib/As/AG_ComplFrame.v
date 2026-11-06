(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FMapPositive.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AsanAllocModel AsanAllocCons SReach LazyRestrict LazyLedger LazySR LazyNodes.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import ASegs AsShadow AllocWf AllocKit AllocBudget AllocRep AllocRepFacts AllocRepFacts2 AllocRepX
     AsDepotInv AW_DepotFrame AllocWalkKit AG_MallocModel AG_WFHit AG_Malloc AG_Malloc2 AG_Frame AG_RepQ AG_WriteSet AG_RecycleDefs SecLazy AllocTacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsbAG_WriteSet~~~~~~hc5awrit79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AllocRep~~~~~~m53ast37Corelib4Init5Logicq93iff79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsaAsDepotInv~~~~~~s35d_puts35depothc6acompl79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AsShadow~~~~~~hhc3mem37Corelib4Init9Datatypeshm13nilhm14prodq93not79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AG_Frame~~~~~~hoe7aclienthoe7amframe79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AseAG_RecycleDefs~~~~~~hu25alivem54a_stm58agree_onm56ast_ok36Stdlib5Lists4Listika2Inm53albq92eqq93andm54a_pam54a_sbm55a_thr69OSSVerify6Proofsaboost_jsonafuzz_parse3libeAsanAllocModel~~~~~~ioa6as_sechm14listioa6schunk79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsaAG_Malloc2~~~~~~iu7cdepot_placedm58AFS_SIZEm55a_fsbm54disj46Stdlib6ZArith6BinInt1Zjl13muls34d_nbs34d_sbhhc5aceiljl12le" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac lia ::=
  first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].

Section HCW.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
Lemma awrit_dput : ltac2:(zQ "60!h9!ld!q3!rd!hg3!hgb>1s$2>2s'$2>1d$5>1h$0>1n$0>2lo$0>2SP$0>1a$0@2$3@6$1^8^7@3$4^6^5^4^3^2^1@6$1^8^7^6^3^2^1").
Proof. intros. unfold awrit. rewrite d_nb_put, d_sb_put. tauto. Qed.
Lemma acompl_dput : ltac2:(zQ "70!h9!hh3!q3!hla!rd!hg3!hgb>1s$2>2s'$2>1d$6>1h$0>1n$0>2lo$0>2SP$0>1m$3>2m'$3@2$4@7$1^9^8@3$5^7^6^5^4^3^2^1@7$1^9^8^7^4^3^2^1").
Proof.
  intros s s' d h n lo SP m m'. unfold acompl. split; intros H a Ha NW; apply (H a Ha); intros W; apply NW.
  - exact (proj1 (awrit_dput s s' d h n lo SP a) W).
  - exact (proj2 (awrit_dput s s' d h n lo SP a) W).
Qed.

(* [comment removed for export] *)

Section ComplFrame.
  Variables (s s1 s2 : ast) (LB : list (Z * Z)) (d : depot) (lo SP : Z) (m1 m2 : mem).
  Hypothesis OK : ltac2:(zQ "10!ik1@2$0?5HCEIL?1s").
  Hypothesis HLB1 : ltac2:(zQ "40!h9!ho0!ild!im3>1b@2$1$0$0>0@3$2@2$1$0$0^1?2LB@3$2@2$1$0$0^2@1$3?2s1").
  Hypothesis E1 : ltac2:(zQ "60!im9!h9!ime!in4!inb!io2@2$2@3$0$1@1$5?2s1@1$5?1s@2$2@3$0$1@1$4?2s1@1$4?1s@3$0$1@1$3?2s1@1$3?1s").
  Hypothesis ES : ltac2:(zQ "50!iif!isb!it5!im9!itd@3$3@1$2$4@1$1@1$0?2s1@1$1@1$0?1s").
  Hypothesis SUB : ltac2:(zQ "40!itd!iif!isb!ild>2sc$0>0@3$3$0^1@1$2@1$1?2s2@3$3$0^2@1$2@1$1?2s1").
  Hypothesis DPL : ltac2:(zQ "10!ji7@3$0?5HCEIL?1s?1d").
  Hypothesis DFS : ltac2:(zQ "70!jj7!jk2!jka!jm9!ime!jn0!jn7@2$4@4$2@1$1?1s$0@1$5?1d@2$3+h0+hggg0@4$2@1$1?1s$0@1$6?1d@2$3+8+ogg0").
  Hypothesis LO : ltac2:(zQ "20!jne!jo7@2$1@1$0?5HCEIL?2lo").
  Hypothesis LS : ltac2:(zQ "10!jo7@2$0?2lo?2SP").

  Let NIL : forall b : Z * Z, In b [] -> In b (alb s). Proof. intros b []. Qed.

  (* [comment removed for export] *)
  Lemma client_not_awrit : ltac2:(zQ "60!h9!hn9!ho0!ho8!hsc!ld>1a$0>0@5$4?5HCEIL?1s@1$1@2$2$0$0?2SP^1@1$3@6$5?2s1?2s2?1d?2lo?2SP^2").
  Proof.
    intros a CL W. ndestruct E1 as (Et & Es & Ep). unfold awrit in W. rewrite Et, Es, Ep in W.
    pose proof (proj1 OK) as PL.
    npose PL as (Y1 & Y2 & Y3 & P1 & P2 & P3 & T1 & T2 & T3 & X1 & X2 & X3 & D1 & D2 & D3 & D4 & D5 & F1 & F2 & D6 & D7 & D8 & D9 & SEC & SEC2 & TCX).
    npose DPL as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
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
      ndestruct W as (sc & IN & R).
      assert (INs : In sc (as_sec (a_st s))) by (destruct IN as [I|I]; [rewrite <- ES; exact I| rewrite <- ES; exact (SUB sc I)]).
      npose (SEC sc INs) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
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
      + refine (apriv_static s OK [] NIL SP 0x292108 0x6a2130 _ SPc _ a W CL); [unfold AIMG_TOP; clear; lia| clear; lia].
      + refine (apriv_static s OK [] NIL SP AIAINIT (AIAINIT + 4) _ SPc _ a W CL); unfold AIAINIT, AIMG_TOP; clear; lia.
      + refine (apriv_static s OK [] NIL SP AIAINST (AIAINST + 0x81030) _ SPc _ a W CL); unfold AIAINST, AIMG_TOP; clear; lia.
    - (* [comment removed for export] *)
      destruct (apriv_depot_blocks s OK [] NIL SP (d_nb d) (d_sb d) G10 G12 G3 G4 G9 (proj1 DFS) (proj2 DFS) SPc) as [AN AS].
      destruct W as [W|W]; [exact (AN a W CL)| exact (AS a W CL)].
  Qed.

  (* [comment removed for export] *)
  Lemma amframe_of_compl : ltac2:(zQ "50!ht7!ii6!hh3!iif!ij6>0@7$2?2s1?2s2?1d?2lo?2SP?2m1?2m2>0@3$4@1$1@1$3?2s1?2m1?2m2@6$0?5HCEIL?1s?2LB?2SP?2m1?2m2").
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
(* [comment removed for export] *)
