(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn LhPure.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit Fz_kit Fz_I1_defs Fz_I1_rep. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_cpy. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_M_malloc Fz_M_zalloc Fz_M_calloc Fz_M_realloc Fz_kit_ra Fz_I2_ppi. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Th_mutex. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_lock Fz_T_sk F_strlen F_memcpy Fz_K_hash Fz_K_rep Fz_K_getrn Fz_K_retrieve Fz_K_insert Fz_K_pstr1 Fz_K_pstr2 Fz_K_pstr3 Fz_K_skstmt Fz_K_pstr Fz_K_pstrf Fz_K_pstrg Fz_I2_ppi2a.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Notation wz := (Z_to_bv 64) (only parsing).
Notation z64 := (Z_to_bv 64 0) (only parsing).

(* [comment removed for export] *)
Ltac wnorm1 f := match goal with |- context [f ?n] => let v := eval vm_compute in (f n) in lazymatch v with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end; change (f n) with v end.
Ltac wnorm := repeat (wnorm1 wA); repeat (wnorm1 wB); repeat (wnorm1 wBig).
Ltac wnormH H := repeat (match type of H with context [wA ?n] => let v := eval vm_compute in (wA n) in change (wA n) with v in H end);
                repeat (match type of H with context [wB ?n] => let v := eval vm_compute in (wB n) in change (wB n) with v in H end);
                repeat (match type of H with context [wBig ?n] => let v := eval vm_compute in (wBig n) in change (wBig n) with v in H end).
(* [comment removed for export] *)
Ltac pneE E := first [ match goal with N : _ <> _ |- _ => first [exact (N E) | exact (N (eq_sym E))] end
                     | match goal with F : forall q, orig _ _ q -> q <> _, O : orig _ _ _ |- _ => first [exact (F _ O E) | exact (F _ O (eq_sym E))] end ].
Ltac pne := first [ assumption | apply not_eq_sym; assumption | let E := fresh "E" in intros E; pneE E ].
(* [comment removed for export] *)
Ltac or_cases tac :=
  hnf;
  lazymatch goal with
  | |- (_ \/ _) -> _ => let X := fresh "X" in intros X; destruct X as [X|X]; revert X; [or_cases tac| or_cases tac]
  | |- False -> _ => intros []
  | |- _ -> _ => let E := fresh "E" in intros E; tac E
  end.
(* [comment removed for export] *)
Ltac ht_leaf q Hq NT E := first
  [ solve [apply NT; subst q; unfold ppk_T, ppk_ids; cbn [In k_ps k_pk k_pl1 k_pb1 k_pl2 k_pb2 k_pq1 k_pq2]; repeat (first [left; reflexivity | right])]
  | match goal with F : forall q0, orig _ _ q0 -> q0 <> _ |- _ => first [exact (F _ Hq E) | exact (F _ Hq (eq_sym E))] end ].


Theorem ossl_property_parse_init_fp_proof : crypto_malloc_stmt -> crypto_calloc_stmt -> T_sk_push_room_stmt -> T_sk_push_grow_stmt -> ossl_property_parse_init_fp_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros CM CC PUSHR PUSHG. unfold ossl_property_parse_init_fp_stmt.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBall LB L f lo Bd KP Hf ROOM CST SLO SP16 EA0 CELL REP0.
  destruct KP as [ps pk pl1 pb1 pl2 pb2 pq1 pq2 S LK lh1 B1 lh2 B2 Q1 Q2].
  cbn [k_ps k_pk k_pl1 k_pb1 k_pl2 k_pb2 k_pq1 k_pq2 a_S a_LK a_lh1 a_B1 a_lh2 a_B2 a_Q1 a_Q2] in *.
  unfold PPI_EV, PPI_NA in *. unfold CTX_PSD in CELL.
  unfold psd_rep, ppk_ids in REP0. cbn [k_ps k_pk k_pl1 k_pb1 k_pl2 k_pb2 k_pq1 k_pq2 a_S a_LK a_lh1 a_B1 a_lh2 a_B2 a_Q1 a_Q2] in REP0.
  destruct REP0 as (OS & SCS & OK & LKC & LH1 & LH2 & OQ1 & QC1 & OQ2 & QC2 & ND8).
  pose proof (plh_rep_of_empty _ _ _ _ _ _ _ LH1) as REPa. pose proof (plh_rep_of_empty _ _ _ _ _ _ _ LH2) as REPb. clear LH1 LH2.
  pose proof (proj1 OS) as INS. pose proof (proj1 OK) as INK. pose proof (proj1 OQ1) as INQ1. pose proof (proj1 OQ2) as INQ2.
  destruct (plh_rep_blocks _ _ _ _ _ _ _ _ _ REPa) as (INL1 & INB1 & _). destruct (plh_rep_blocks _ _ _ _ _ _ _ _ _ REPb) as (INL2 & INB2 & _).
  pose proof (orig_of_in _ L _ _ _ INS) as Ops. pose proof (orig_of_in _ L _ _ _ INK) as Opk. pose proof (orig_of_in _ L _ _ _ INQ1) as Opq1. pose proof (orig_of_in _ L _ _ _ INQ2) as Opq2.
  pose proof (orig_of_in _ L _ _ _ INL1) as Opl1. pose proof (orig_of_in _ L _ _ _ INB1) as Opb1. pose proof (orig_of_in _ L _ _ _ INL2) as Opl2. pose proof (orig_of_in _ L _ _ _ INB2) as Opb2.
  (* [comment removed for export] *)
  pose proof (nd_neq _ 7 6 _ _ ND8 eq_refl eq_refl ltac:(discriminate)) as NSK. pose proof (nd_neq _ 7 1 _ _ ND8 eq_refl eq_refl ltac:(discriminate)) as NSQ1.
  pose proof (nd_neq _ 7 0 _ _ ND8 eq_refl eq_refl ltac:(discriminate)) as NSQ2. pose proof (nd_neq _ 7 5 _ _ ND8 eq_refl eq_refl ltac:(discriminate)) as NSL1.
  pose proof (nd_neq _ 7 4 _ _ ND8 eq_refl eq_refl ltac:(discriminate)) as NSB1. pose proof (nd_neq _ 7 3 _ _ ND8 eq_refl eq_refl ltac:(discriminate)) as NSL2.
  pose proof (nd_neq _ 7 2 _ _ ND8 eq_refl eq_refl ltac:(discriminate)) as NSB2.
  pose proof (nd_neq _ 6 1 _ _ ND8 eq_refl eq_refl ltac:(discriminate)) as NKQ1. pose proof (nd_neq _ 6 0 _ _ ND8 eq_refl eq_refl ltac:(discriminate)) as NKQ2.
  pose proof (nd_neq _ 6 5 _ _ ND8 eq_refl eq_refl ltac:(discriminate)) as NKL1. pose proof (nd_neq _ 6 4 _ _ ND8 eq_refl eq_refl ltac:(discriminate)) as NKB1.
  pose proof (nd_neq _ 6 3 _ _ ND8 eq_refl eq_refl ltac:(discriminate)) as NKL2. pose proof (nd_neq _ 6 2 _ _ ND8 eq_refl eq_refl ltac:(discriminate)) as NKB2.
  pose proof (nd_neq _ 1 5 _ _ ND8 eq_refl eq_refl ltac:(discriminate)) as NQ1L1. pose proof (nd_neq _ 1 4 _ _ ND8 eq_refl eq_refl ltac:(discriminate)) as NQ1B1.
  pose proof (nd_neq _ 1 3 _ _ ND8 eq_refl eq_refl ltac:(discriminate)) as NQ1L2. pose proof (nd_neq _ 1 2 _ _ ND8 eq_refl eq_refl ltac:(discriminate)) as NQ1B2.
  pose proof (nd_neq _ 1 0 _ _ ND8 eq_refl eq_refl ltac:(discriminate)) as NQ1Q2.
  pose proof (nd_neq _ 0 5 _ _ ND8 eq_refl eq_refl ltac:(discriminate)) as NQ2L1. pose proof (nd_neq _ 0 4 _ _ ND8 eq_refl eq_refl ltac:(discriminate)) as NQ2B1.
  pose proof (nd_neq _ 0 3 _ _ ND8 eq_refl eq_refl ltac:(discriminate)) as NQ2L2. pose proof (nd_neq _ 0 2 _ _ ND8 eq_refl eq_refl ltac:(discriminate)) as NQ2B2.
  pose proof (nd_neq _ 5 3 _ _ ND8 eq_refl eq_refl ltac:(discriminate)) as NL1L2. pose proof (nd_neq _ 5 2 _ _ ND8 eq_refl eq_refl ltac:(discriminate)) as NL1B2.
  pose proof (nd_neq _ 4 3 _ _ ND8 eq_refl eq_refl ltac:(discriminate)) as NB1L2. pose proof (nd_neq _ 4 2 _ _ ND8 eq_refl eq_refl ltac:(discriminate)) as NB1B2.
  pose proof CST as (HP & CO & (errv & AV & SPB & ST & LO & ERR & MI & TP) & LXS & LATCH & CIMG & GLO).
  unfold PPI_STACK, PSTR_STACK, SK_PUSH_GROW_STACK, CRE_STACK, RREALLOC_STACK, RMALLOC_STACK, GLOBALS_TOP in *.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (CW : alloc_ceiling < 2^63) by (unfold ceil_window in *; lia). assert (SP0 : 8544 <= bv_unsigned sp) by (clear - SLO GLO; lia).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST INS) as (Sg0 & _ & _ & SC48 & _). pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST INK) as (LKg0 & _ & _ & LKC40 & _).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST INQ1) as (Q1g0 & _ & _ & Q1C & _). pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST INQ2) as (Q2g0 & _ & _ & Q2C & _).
  pose proof (rw_cells_bound _ _ _ _ CELL) as CELLB. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in CELLB. unfold CTX_A in CELLB.
  (* [comment removed for export] *)
  eapply climpl_evt. { eapply (ppi_seg0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m lo); [exact EA0| exact ST| clear - LO Sg0 SC48; lia| clear - SLO; lia| exact MI]. }
  cbv beta. intros ms1 (m1 & -> & MU01 & WM01 & MI1 & ST1 & FRs0).
  assert (CSTs0 : cstate s LBall LB L m1 (Z_to_bv 64 (bv_unsigned sp + -48)) tp lo Bd).
  { eapply (cstate_seg _ _ _ _ _ m m1 _ _ tp lo Bd (bv_unsigned sp)); [exact CST| exact MU01| exact WM01| exact MI1| | clear - SPR SLO LO GLO; lia| exact SPB| | rewrite unsigned_lit by (clear - SPR SP0; lia); exact ST1| rewrite unsigned_lit by (clear - SPR SP0; lia); clear - SPB SPR SP0; lia].
    - constructor; [apply cwin_stack; clear - SPR SLO LO GLO; lia| constructor].
    - cbn [disjoint_from]. unfold LX_FLAGS. clear - SPR GLO SLO. lia. }
  assert (FRM1 : cframe (ppk_T (PPK ps pk pl1 pb1 pl2 pb2 pq1 pq2 S LK lh1 B1 lh2 B2 Q1 Q2)) [] (bv_unsigned sp) s LBall L m s LBall L m1).
  { eapply cframe_seg; [apply cframe_refl| exact MU01| exact WM01| exact HP| clear - LO SLO SPR GLO; lia|]. constructor; [apply cseg_ok_stack; clear - LO SLO SPR GLO; lia| constructor]. }
  assert (SCS1 : rw_cells usegs m1 S (psd_cells LK lh1 lh2 0 0 Q1 Q2)).
  { eapply rw_cells_transport; [exact SCS| exact MU01| exact WM01|]. unfold psd_cells. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. clear - SLO LO SC48. lia. }
  assert (LKC1 : rw_cells usegs m1 LK (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))).
  { eapply rw_cells_transport; [exact LKC| exact MU01| exact WM01|]. unfold mutex_cells. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. clear - SLO LO LKC40. lia. }
  assert (QC11 : rw_cells usegs m1 Q1 (sk_cells (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 PROP_SK_CMPT) (Z_to_bv 64 PROP_SK_FREET) (Z_to_bv 64 PROP_SK_COPYT))).
  { eapply rw_cells_transport; [exact QC1| exact MU01| exact WM01|]. unfold sk_cells. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. clear - SLO LO Q1C. lia. }
  assert (QCos0 : rw_cells usegs m1 Q2 (sk_cells (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 PROP_SK_CMPT) (Z_to_bv 64 PROP_SK_FREET) (Z_to_bv 64 PROP_SK_COPYT))).
  { eapply rw_cells_transport; [exact QC2| exact MU01| exact WM01|]. unfold sk_cells. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. clear - SLO LO Q2C. lia. }
  assert (CELLs0 : rw_cells usegs m1 (CTX_A + 168) [C8 (Z_to_bv 64 S)]).
  { eapply rw_cells_transport; [exact CELL| exact MU01| exact WM01|]. unfold CTX_A. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. clear - SLO GLO. lia. }
  assert (REPa1 : plh_rep m1 LBall L lh1 pl1 pb1 B1 0 (nb16 [] [] [] [] [])).
  { rewrite <- nb16_empty. eapply plh_rep_munch; [exact REPa| exact MU01| exact WM01|]. intros a Ha. cbn [outside]. clear - Ha LO SLO. lia. }
  assert (REPos0 : plh_rep m1 LBall L lh2 pl2 pb2 B2 0 (nb16 [] [] [] [] [])).
  { rewrite <- nb16_empty. eapply plh_rep_munch; [exact REPb| exact MU01| exact WM01|]. intros a Ha. cbn [outside]. clear - Ha LO SLO. lia. }
  clear SCS LKC QC1 QC2 REPa REPb.
  (* [comment removed for export] *)
  pose proof lit_provider as (ROB & NONUL & NE & PAD & SLOW & SHIGH & LEN).
  eapply climpl_seq.
  { eapply (pstr_first_true CM CC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 s LBall LB L f lo Bd CTX_A S LK lh1 lh2 0 0 Q1 Q2 A_PROVIDER s_provider k_provider ps pk pq1 pl1 pb1 B1 0 (nb16 [] [] [] [] []));
      [clear - Hf; lia| | exact CSTs0| rewrite unsigned_lit by (clear - SPR SP0; lia); unfold PSTR_STACK, SK_PUSH_GROW_STACK, CRE_STACK, RREALLOC_STACK, RMALLOC_STACK; clear - SLO; lia
      | reflexivity| reflexivity| reflexivity| reflexivity| unfold CTX_A; clear; lia| unfold CTX_A; clear; lia| exact CELLs0| unfold CTX_A; clear; lia
      | rewrite unsigned_lit by (clear - SPR SP0; lia); clear - SP16; lia
      | exact INS| exact SCS1| clear; lia| clear; lia| clear; lia| clear; lia| exact INK| exact LKC1| exact REPa1| clear; lia
      | rewrite hash_provider; cbn; constructor
      | exact INQ1| exact QC11| exact ROB| exact NONUL| exact NE| exact PAD| exact SLOW| exact SHIGH| exact LEN
      | unfold plh_T; cbn [map concat nb16 app In]; intros [E|[E|[]]]; pneE E
      | unfold plh_T; cbn [map concat nb16 app In]; intros [E|[E|[]]]; pneE E
      | unfold plh_T; cbn [map concat nb16 app In]; intros [E|[E|[]]]; pneE E
      | pne| pne| pne].
    eapply croom_weaken; [exact ROOM| | |]; wnorm; clear; lia. }
  cbv beta. intros f1 L1 st1 msr1 (v1 & m2 & LB1r & RET1 & FU1 & GR1 & CSTc1 & FRMc1 & RES1).
  destruct RES1 as (pn1 & An1 & pd1 & D1 & pnn1 & N1 & RES1). cbv zeta in RES1. rewrite hash_provider in RES1.
  destruct RES1 as (-> & -> & -> & RA1 & RD1 & RN1 & SCSc1 & LKCc1 & REPc1 & QCc1 & DCc1 & _).
  destruct RET1 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->). cret_lit.
  wnormH GR1. pose proof GR1 as GA1.
  (* [comment removed for export] *)
  change (Z.of_nat (length s_provider) + 16) with 24 in *. change (cnt_of true 0 0 + 1) with 1 in *. cbn [ni_after vi_after t_of q_of] in SCSc1, REPc1, QCc1.
  change (0 + 1) with 1 in REPc1.
  change (lupd (Z.to_nat (H_PROVIDER mod 8)) (nth (Z.to_nat (H_PROVIDER mod 8)) (nb16 [] [] [] [] []) [] ++ [(pnn1, N1, H_PROVIDER)]) (nb16 [] [] [] [] [])) with (nb16 [] [(pnn1, N1, H_PROVIDER)] [] [] []) in REPc1.
  set (LB1 := (pnn1, N1, 24) :: (pd1, D1, 32) :: (pn1, An1, 24) :: LBall) in *. set (L1 := (pnn1, 24) :: (pd1, 32) :: (pn1, 24) :: L) in *.
  pose proof CSTc1 as (HPc1 & _ & (errc1 & _ & _ & STc1 & _ & _ & MIc1 & _) & _). rewrite unsigned_lit in STc1 by (clear - SPR SP0; lia).
  pose proof FRMc1 as (CFRc1 & _). rewrite unsigned_lit in CFRc1 by (clear - SPR SP0; lia).
  destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CSTc1) as [NDL1 _]. subst LB1. cbn [map blk_id fst] in NDL1.
  pose proof (cstate_fresh_ids st1 [(pnn1, N1, 24); (pd1, D1, 32); (pn1, An1, 24)] LBall LB L _ m2 _ _ _ _ CSTc1 CO) as FRa.
  pose proof (fun q (Hq : orig LBall L q) => FRa (pnn1, N1, 24) (or_introl eq_refl) q Hq) as Fpnn1. cbn [blk_id fst] in Fpnn1.
  pose proof (fun q (Hq : orig LBall L q) => FRa (pd1, D1, 32) (or_intror (or_introl eq_refl)) q Hq) as Fpd1. cbn [blk_id fst] in Fpd1.
  clear FRa.
  pose proof (nd_neq _ 1 0 _ _ NDL1 eq_refl eq_refl ltac:(discriminate)) as Npd1pnn1.
  set (LB1 := (pnn1, N1, 24) :: (pd1, D1, 32) :: (pn1, An1, 24) :: LBall) in *.
  assert (INS_1 : In (ps, S, 48) LB1) by (do 3 right; exact INS). assert (INK_1 : In (pk, LK, 40) LB1) by (do 3 right; exact INK).
  assert (INQ1_1 : In (pq1, Q1, 56) LB1) by (do 3 right; exact INQ1). assert (INQ2_1 : In (pq2, Q2, 56) LB1) by (do 3 right; exact INQ2).
  assert (IND_1 : In (pd1, D1, 32) LB1) by (do 1 right; left; reflexivity).
  assert (FRMo1 : cframe (ppk_T (PPK ps pk pl1 pb1 pl2 pb2 pq1 pq2 S LK lh1 B1 lh2 B2 Q1 Q2)) [] (bv_unsigned sp) s LBall L m st1 LB1 L1 m2).
  { eapply cframe_call; [exact FRM1| exact FRMc1| rewrite unsigned_lit by (clear - SPR SP0; lia); clear; lia| intros a X; exact X|].
    intros q Hq NT. unfold pstr_T1, plh_T. cbn [map concat nb16 app In]. or_cases ltac:(fun E => ht_leaf q Hq NT E). }
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFRc1 FRs0 ltac:(clear; lia)) as FRc1.
  assert (CELLc1 := cfr_cells_static _ _ _ _ _ _ _ _ CFRc1 CELLs0). cbn [cells_size csize Nat.add] in CELLc1. unfold CTX_A in CELLc1.
  specialize (CELLc1 ltac:(clear; lia) ltac:(clear; lia) ltac:(intros a Ha; unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP, LX_FLAGS; cbn [rin_ivs fst snd]; clear - Ha; lia)).
  assert (REPoc1 : plh_rep m2 LB1 L1 lh2 pl2 pb2 B2 0 (nb16 [] [] [] [] [])).
  { eapply plh_rep_cframe; [exact REPos0| exact FRMc1|]. unfold pstr_T1, plh_T. cbn [map concat nb16 app In]. intros q [<-|[<-|[]]]; or_cases ltac:(fun E => pneE E). }
  assert (QCoc1 := cfr_cells_block _ _ _ _ _ _ _ _ (pq2, Q2, 56) CFRc1 QCos0 INQ2). unfold blk_id, blk_addr, blk_size, sk_cells in QCoc1. cbn [fst snd cells_size csize Nat.add] in QCoc1.
  specialize (QCoc1 ltac:(unfold pstr_T1, plh_T; cbn [map concat nb16 app In]; or_cases ltac:(fun E => pneE E)) ltac:(clear; lia) ltac:(clear; lia)).
  clear FRs0 CELLs0 CSTs0 REPos0 QCos0 FRMc1 CFRc1 FRM1 SCS1 LKC1 REPa1 QC11.
  (* [comment removed for export] *)
  eapply climpl_evt. { eapply (ppi_seg1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 lo); [exact STc1| clear - LO Sg0 SC48; lia| clear - SLO; lia| clear - SP0; lia| exact MIc1]. }
  cbv beta. intros ms2 (m3 & -> & MU1 & WM1 & MIs1 & STs1).
  assert (CSTs1 : cstate st1 LB1 LB L1 m3 (Z_to_bv 64 (bv_unsigned sp + -48)) tp lo Bd).
  { eapply (cstate_seg _ _ _ _ _ m2 m3 _ _ tp lo Bd (bv_unsigned sp + -48)); [exact CSTc1| exact MU1| exact WM1| exact MIs1| | clear - SPR SLO LO GLO; lia| clear - SPB SP0; lia| | rewrite unsigned_lit by (clear - SPR SP0; lia); exact STs1| rewrite unsigned_lit by (clear - SPR SP0; lia); clear - SPB SPR SP0; lia].
    - constructor; [apply cwin_stack; clear - SPR SLO LO GLO; lia| constructor].
    - cbn [disjoint_from]. unfold LX_FLAGS. clear - SPR GLO SLO. lia. }
  assert (FRMs1 : cframe (ppk_T (PPK ps pk pl1 pb1 pl2 pb2 pq1 pq2 S LK lh1 B1 lh2 B2 Q1 Q2)) [] (bv_unsigned sp) s LBall L m st1 LB1 L1 m3).
  { eapply cframe_seg; [exact FRMo1| exact MU1| exact WM1| exact HPc1| clear - LO SLO SPR GLO; lia|]. constructor; [apply cseg_ok_stack; clear - LO SLO SPR GLO; lia| constructor]. }
  assert (FRs1 : rw_cells usegs m3 (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { eapply rw_cells_transport; [exact FRc1| exact MU1| exact WM1|]. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. clear - SPR SP0. lia. }
  assert (CELLs1 : rw_cells usegs m3 (CTX_A + 168) [C8 (Z_to_bv 64 S)]).
  { eapply rw_cells_transport; [exact CELLc1| exact MU1| exact WM1|]. unfold CTX_A. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. clear - SLO GLO. lia. }
  assert (SCSs1 : rw_cells usegs m3 S (psd_cells LK lh1 lh2 1 0 Q1 Q2)).
  { eapply rw_cells_transport; [exact SCSc1| exact MU1| exact WM1|]. unfold psd_cells. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. clear - SLO LO SC48. lia. }
  assert (LKCs1 : rw_cells usegs m3 LK (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))).
  { eapply rw_cells_transport; [exact LKCc1| exact MU1| exact WM1|]. unfold mutex_cells. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. clear - SLO LO LKC40. lia. }
  assert (QCs1 : rw_cells usegs m3 Q1 (sk_cells (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 D1) (Z_to_bv 64 1) (Z_to_bv 64 4) (Z_to_bv 64 0) (Z_to_bv 64 PROP_SK_CMPT) (Z_to_bv 64 PROP_SK_FREET) (Z_to_bv 64 PROP_SK_COPYT))).
  { eapply rw_cells_transport; [exact QCc1| exact MU1| exact WM1|]. unfold sk_cells. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. clear - SLO LO Q1C. lia. }
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CSTc1 IND_1) as (Dg0_1 & _ & _ & DCg_1 & _).
  assert (DCs1 : rw_cells usegs m3 D1 [CB (8 + 24)%nat (le8 (Z_to_bv 64 (An1 + 12)) ++ repeat (Z_to_bv 8 0) 24)]).
  { apply cells_C8_CB; [reflexivity|]. eapply rw_cells_transport; [exact DCc1| exact MU1| exact WM1|]. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. clear - SLO LO DCg_1. lia. }
  assert (REPs1 : plh_rep m3 LB1 L1 lh1 pl1 pb1 B1 1 (nb16 [] [(pnn1, N1, H_PROVIDER)] [] [] [])).
  { eapply plh_rep_munch; [exact REPc1| exact MU1| exact WM1|]. intros a Ha. cbn [outside]. clear - Ha LO SLO. lia. }
  assert (REPos1 : plh_rep m3 LB1 L1 lh2 pl2 pb2 B2 0 (nb16 [] [] [] [] [])).
  { eapply plh_rep_munch; [exact REPoc1| exact MU1| exact WM1|]. intros a Ha. cbn [outside]. clear - Ha LO SLO. lia. }
  assert (QCos1 : rw_cells usegs m3 Q2 (sk_cells (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 PROP_SK_CMPT) (Z_to_bv 64 PROP_SK_FREET) (Z_to_bv 64 PROP_SK_COPYT))).
  { eapply rw_cells_transport; [exact QCoc1| exact MU1| exact WM1|]. unfold sk_cells. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. clear - SLO LO Q2C. lia. }
  clear FRc1 CELLc1 SCSc1 LKCc1 CSTc1 FRMo1 HPc1 STc1 MIc1 MU1 WM1 QCc1 DCc1 REPc1 REPoc1 QCoc1.
  (* [comment removed for export] *)
  clear ROB NONUL NE PAD SLOW SHIGH LEN. pose proof lit_version as (ROB & NONUL & NE & PAD & SLOW & SHIGH & LEN).
  eapply climpl_seq.
  { eapply (pstr_room_true CM PUSHR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 st1 LB1 LB L1 f1 lo Bd CTX_A S LK lh1 lh2 1 0 Q1 Q2 A_VERSION s_version k_version ps pk pq1 pd1 pl1 pb1 B1 1 (nb16 [] [(pnn1, N1, H_PROVIDER)] [] [] []) D1 1 4 1);
      [clear - Hf FU1; lia| | exact CSTs1| rewrite unsigned_lit by (clear - SPR SP0; lia); unfold PSTR_STACK, SK_PUSH_GROW_STACK, CRE_STACK, RREALLOC_STACK, RMALLOC_STACK; clear - SLO; lia
      | reflexivity| reflexivity| reflexivity| reflexivity| unfold CTX_A; clear; lia| unfold CTX_A; clear; lia| exact CELLs1| unfold CTX_A; clear; lia
      | rewrite unsigned_lit by (clear - SPR SP0; lia); clear - SP16; lia
      | exact INS_1| exact SCSs1| clear; lia| clear; lia| clear; lia| clear; lia| exact INK_1| exact LKCs1| exact REPs1| clear; lia
      | rewrite hash_version; cbn; repeat (constructor; [discriminate|]); constructor
      | exact INQ1_1| exact QCs1| clear; lia| clear; lia| clear; lia| clear; lia| exact IND_1| exact DCs1
      | exact ROB| exact NONUL| exact NE| exact PAD| exact SLOW| exact SHIGH| exact LEN
      | unfold plh_T; cbn [map concat nb16 app In]; or_cases ltac:(fun E => pneE E)| unfold plh_T; cbn [map concat nb16 app In]; or_cases ltac:(fun E => pneE E)| unfold plh_T; cbn [map concat nb16 app In]; or_cases ltac:(fun E => pneE E)| unfold plh_T; cbn [map concat nb16 app In]; or_cases ltac:(fun E => pneE E)
      | pne| pne| pne| pne| pne| pne].
    eapply croom_weaken; [eapply croom_grow; [exact ROOM| exact GA1]| | |]; wnorm; clear; lia. }
  cbv beta. intros f2 L2r st2 msr2 (v2 & m4 & LB2r & RET2 & FU2 & GR2 & CSTc2 & FRMc2 & RES).
  destruct RES as (pn2 & An2 & pnn2 & N2 & jk2 & RES). cbv zeta in RES. rewrite hash_version in RES.
  destruct RES as (-> & -> & -> & RA2 & RN2 & SCSc2 & LKCc2 & REPc2 & QCc2 & DCc2 & _).
  destruct RET2 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->). cret_lit.
  wnormH GR2. pose proof (cgrow_trans _ _ _ _ _ _ _ _ _ GA1 GR2) as GA2. clear GR2.
  (* [comment removed for export] *)
  change (Z.of_nat (length s_version) + 16) with 23 in *. change (cnt_of true 1 0 + 1) with 2 in *. cbn [ni_after vi_after t_of q_of] in SCSc2, REPc2, QCc2.
  change (1 + 1) with 2 in REPc2.
  change (lupd (Z.to_nat (H_VERSION mod 8)) (nth (Z.to_nat (H_VERSION mod 8)) (nb16 [] [(pnn1, N1, H_PROVIDER)] [] [] []) [] ++ [(pnn2, N2, H_VERSION)]) (nb16 [] [(pnn1, N1, H_PROVIDER)] [] [] [])) with (nb16 [] [(pnn1, N1, H_PROVIDER); (pnn2, N2, H_VERSION)] [] [] []) in REPc2.
  set (LB2 := (pnn2, N2, 24) :: (pn2, An2, 23) :: (pnn1, N1, 24) :: (pd1, D1, 32) :: (pn1, An1, 24) :: LBall) in *. set (L2 := (pnn2, 24) :: (pn2, 23) :: (pnn1, 24) :: (pd1, 32) :: (pn1, 24) :: L) in *.
  pose proof CSTc2 as (HPc2 & _ & (errc2 & _ & _ & STc2 & _ & _ & MIc2 & _) & _). rewrite unsigned_lit in STc2 by (clear - SPR SP0; lia).
  pose proof FRMc2 as (CFRc2 & _). rewrite unsigned_lit in CFRc2 by (clear - SPR SP0; lia).
  destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CSTc2) as [NDL2 _]. subst LB2. cbn [map blk_id fst] in NDL2.
  pose proof (cstate_fresh_ids st2 [(pnn2, N2, 24); (pn2, An2, 23); (pnn1, N1, 24); (pd1, D1, 32); (pn1, An1, 24)] LBall LB L _ m4 _ _ _ _ CSTc2 CO) as FRa.
  pose proof (fun q (Hq : orig LBall L q) => FRa (pnn2, N2, 24) (or_introl eq_refl) q Hq) as Fpnn2. cbn [blk_id fst] in Fpnn2.
  clear FRa.
  pose proof (nd_neq _ 3 0 _ _ NDL2 eq_refl eq_refl ltac:(discriminate)) as Npd1pnn2.
  set (LB2 := (pnn2, N2, 24) :: (pn2, An2, 23) :: (pnn1, N1, 24) :: (pd1, D1, 32) :: (pn1, An1, 24) :: LBall) in *.
  assert (INS_2 : In (ps, S, 48) LB2) by (do 5 right; exact INS). assert (INK_2 : In (pk, LK, 40) LB2) by (do 5 right; exact INK).
  assert (INQ1_2 : In (pq1, Q1, 56) LB2) by (do 5 right; exact INQ1). assert (INQ2_2 : In (pq2, Q2, 56) LB2) by (do 5 right; exact INQ2).
  assert (IND_2 : In (pd1, D1, 32) LB2) by (do 3 right; left; reflexivity).
  assert (FRMo2 : cframe (ppk_T (PPK ps pk pl1 pb1 pl2 pb2 pq1 pq2 S LK lh1 B1 lh2 B2 Q1 Q2)) [] (bv_unsigned sp) s LBall L m st2 LB2 L2 m4).
  { eapply cframe_call; [exact FRMs1| exact FRMc2| rewrite unsigned_lit by (clear - SPR SP0; lia); clear; lia| intros a X; exact X|].
    intros q Hq NT. unfold pstr_T, plh_T. cbn [map concat nb16 app In]. or_cases ltac:(fun E => ht_leaf q Hq NT E). }
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFRc2 FRs1 ltac:(clear; lia)) as FRc2.
  assert (CELLc2 := cfr_cells_static _ _ _ _ _ _ _ _ CFRc2 CELLs1). cbn [cells_size csize Nat.add] in CELLc2. unfold CTX_A in CELLc2.
  specialize (CELLc2 ltac:(clear; lia) ltac:(clear; lia) ltac:(intros a Ha; unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP, LX_FLAGS; cbn [rin_ivs fst snd]; clear - Ha; lia)).
  assert (REPoc2 : plh_rep m4 LB2 L2 lh2 pl2 pb2 B2 0 (nb16 [] [] [] [] [])).
  { eapply plh_rep_cframe; [exact REPos1| exact FRMc2|]. unfold pstr_T, plh_T. cbn [map concat nb16 app In]. intros q [<-|[<-|[]]]; or_cases ltac:(fun E => pneE E). }
  assert (QCoc2 := cfr_cells_block _ _ _ _ _ _ _ _ (pq2, Q2, 56) CFRc2 QCos1 INQ2_1). unfold blk_id, blk_addr, blk_size, sk_cells in QCoc2. cbn [fst snd cells_size csize Nat.add] in QCoc2.
  specialize (QCoc2 ltac:(unfold pstr_T, plh_T; cbn [map concat nb16 app In]; or_cases ltac:(fun E => pneE E)) ltac:(clear; lia) ltac:(clear; lia)).
  clear FRs1 CELLs1 CSTs1 REPos1 QCos1 FRMc2 CFRc2 FRMs1.
  (* [comment removed for export] *)
  eapply climpl_evt. { eapply (ppi_seg2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m4 lo); [exact STc2| clear - LO Sg0 SC48; lia| clear - SLO; lia| clear - SP0; lia| exact MIc2]. }
  cbv beta. intros ms3 (m5 & -> & MU2 & WM2 & MIs2 & STs2).
  assert (CSTs2 : cstate st2 LB2 LB L2 m5 (Z_to_bv 64 (bv_unsigned sp + -48)) tp lo Bd).
  { eapply (cstate_seg _ _ _ _ _ m4 m5 _ _ tp lo Bd (bv_unsigned sp + -48)); [exact CSTc2| exact MU2| exact WM2| exact MIs2| | clear - SPR SLO LO GLO; lia| clear - SPB SP0; lia| | rewrite unsigned_lit by (clear - SPR SP0; lia); exact STs2| rewrite unsigned_lit by (clear - SPR SP0; lia); clear - SPB SPR SP0; lia].
    - constructor; [apply cwin_stack; clear - SPR SLO LO GLO; lia| constructor].
    - cbn [disjoint_from]. unfold LX_FLAGS. clear - SPR GLO SLO. lia. }
  assert (FRMs2 : cframe (ppk_T (PPK ps pk pl1 pb1 pl2 pb2 pq1 pq2 S LK lh1 B1 lh2 B2 Q1 Q2)) [] (bv_unsigned sp) s LBall L m st2 LB2 L2 m5).
  { eapply cframe_seg; [exact FRMo2| exact MU2| exact WM2| exact HPc2| clear - LO SLO SPR GLO; lia|]. constructor; [apply cseg_ok_stack; clear - LO SLO SPR GLO; lia| constructor]. }
  assert (FRs2 : rw_cells usegs m5 (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { eapply rw_cells_transport; [exact FRc2| exact MU2| exact WM2|]. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. clear - SPR SP0. lia. }
  assert (CELLs2 : rw_cells usegs m5 (CTX_A + 168) [C8 (Z_to_bv 64 S)]).
  { eapply rw_cells_transport; [exact CELLc2| exact MU2| exact WM2|]. unfold CTX_A. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. clear - SLO GLO. lia. }
  assert (SCSs2 : rw_cells usegs m5 S (psd_cells LK lh1 lh2 2 0 Q1 Q2)).
  { eapply rw_cells_transport; [exact SCSc2| exact MU2| exact WM2|]. unfold psd_cells. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. clear - SLO LO SC48. lia. }
  assert (LKCs2 : rw_cells usegs m5 LK (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))).
  { eapply rw_cells_transport; [exact LKCc2| exact MU2| exact WM2|]. unfold mutex_cells. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. clear - SLO LO LKC40. lia. }
  assert (QCs2 : rw_cells usegs m5 Q1 (sk_cells (Z_to_bv 64 2) (Z_to_bv 64 0) (Z_to_bv 64 D1) (Z_to_bv 64 0) (Z_to_bv 64 4) (Z_to_bv 64 0) (Z_to_bv 64 PROP_SK_CMPT) (Z_to_bv 64 PROP_SK_FREET) (Z_to_bv 64 PROP_SK_COPYT))).
  { eapply rw_cells_transport; [exact QCc2| exact MU2| exact WM2|]. unfold sk_cells. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. clear - SLO LO Q1C. lia. }
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CSTc2 IND_2) as (Dg0_2 & _ & _ & DCg_2 & _).
  assert (DCs2 : rw_cells usegs m5 D1 [CB 32%nat jk2]).
  { eapply rw_cells_transport; [exact DCc2| exact MU2| exact WM2|]. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. clear - SLO LO DCg_2. lia. }
  assert (REPs2 : plh_rep m5 LB2 L2 lh1 pl1 pb1 B1 2 (nb16 [] [(pnn1, N1, H_PROVIDER); (pnn2, N2, H_VERSION)] [] [] [])).
  { eapply plh_rep_munch; [exact REPc2| exact MU2| exact WM2|]. intros a Ha. cbn [outside]. clear - Ha LO SLO. lia. }
  assert (REPos2 : plh_rep m5 LB2 L2 lh2 pl2 pb2 B2 0 (nb16 [] [] [] [] [])).
  { eapply plh_rep_munch; [exact REPoc2| exact MU2| exact WM2|]. intros a Ha. cbn [outside]. clear - Ha LO SLO. lia. }
  assert (QCos2 : rw_cells usegs m5 Q2 (sk_cells (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 PROP_SK_CMPT) (Z_to_bv 64 PROP_SK_FREET) (Z_to_bv 64 PROP_SK_COPYT))).
  { eapply rw_cells_transport; [exact QCoc2| exact MU2| exact WM2|]. unfold sk_cells. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. clear - SLO LO Q2C. lia. }
  clear FRc2 CELLc2 SCSc2 LKCc2 CSTc2 FRMo2 HPc2 STc2 MIc2 MU2 WM2 QCc2 DCc2 REPc2 REPoc2 QCoc2.
  (* [comment removed for export] *)
  clear ROB NONUL NE PAD SLOW SHIGH LEN. pose proof lit_fips as (ROB & NONUL & NE & PAD & SLOW & SHIGH & LEN).
  eapply climpl_seq.
  { eapply (pstr_room_true CM PUSHR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 st2 LB2 LB L2 f2 lo Bd CTX_A S LK lh1 lh2 2 0 Q1 Q2 A_FIPS s_fips k_fips ps pk pq1 pd1 pl1 pb1 B1 2 (nb16 [] [(pnn1, N1, H_PROVIDER); (pnn2, N2, H_VERSION)] [] [] []) D1 2 4 0);
      [clear - Hf FU1 FU2; lia| | exact CSTs2| rewrite unsigned_lit by (clear - SPR SP0; lia); unfold PSTR_STACK, SK_PUSH_GROW_STACK, CRE_STACK, RREALLOC_STACK, RMALLOC_STACK; clear - SLO; lia
      | reflexivity| reflexivity| reflexivity| reflexivity| unfold CTX_A; clear; lia| unfold CTX_A; clear; lia| exact CELLs2| unfold CTX_A; clear; lia
      | rewrite unsigned_lit by (clear - SPR SP0; lia); clear - SP16; lia
      | exact INS_2| exact SCSs2| clear; lia| clear; lia| clear; lia| clear; lia| exact INK_2| exact LKCs2| exact REPs2| clear; lia
      | rewrite hash_fips; cbn; repeat (constructor; [discriminate|]); constructor
      | exact INQ1_2| exact QCs2| clear; lia| clear; lia| clear; lia| clear; lia| exact IND_2| exact DCs2
      | exact ROB| exact NONUL| exact NE| exact PAD| exact SLOW| exact SHIGH| exact LEN
      | unfold plh_T; cbn [map concat nb16 app In]; or_cases ltac:(fun E => pneE E)| unfold plh_T; cbn [map concat nb16 app In]; or_cases ltac:(fun E => pneE E)| unfold plh_T; cbn [map concat nb16 app In]; or_cases ltac:(fun E => pneE E)| unfold plh_T; cbn [map concat nb16 app In]; or_cases ltac:(fun E => pneE E)
      | pne| pne| pne| pne| pne| pne].
    eapply croom_weaken; [eapply croom_grow; [exact ROOM| exact GA2]| | |]; wnorm; clear; lia. }
  cbv beta. intros f3 L3r st3 msr3 (v3 & m6 & LB3r & RET3 & FU3 & GR3 & CSTc3 & FRMc3 & RES).
  destruct RES as (pn3 & An3 & pnn3 & N3 & jk3 & RES). cbv zeta in RES. rewrite hash_fips in RES.
  destruct RES as (-> & -> & -> & RA3 & RN3 & SCSc3 & LKCc3 & REPc3 & QCc3 & DCc3 & _).
  destruct RET3 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->). cret_lit.
  wnormH GR3. pose proof (cgrow_trans _ _ _ _ _ _ _ _ _ GA2 GR3) as GA3. clear GR3.
  (* [comment removed for export] *)
  change (Z.of_nat (length s_fips) + 16) with 20 in *. change (cnt_of true 2 0 + 1) with 3 in *. cbn [ni_after vi_after t_of q_of] in SCSc3, REPc3, QCc3.
  change (2 + 1) with 3 in REPc3.
  change (lupd (Z.to_nat (H_FIPS mod 8)) (nth (Z.to_nat (H_FIPS mod 8)) (nb16 [] [(pnn1, N1, H_PROVIDER); (pnn2, N2, H_VERSION)] [] [] []) [] ++ [(pnn3, N3, H_FIPS)]) (nb16 [] [(pnn1, N1, H_PROVIDER); (pnn2, N2, H_VERSION)] [] [] [])) with (nb16 [] [(pnn1, N1, H_PROVIDER); (pnn2, N2, H_VERSION)] [] [] [(pnn3, N3, H_FIPS)]) in REPc3.
  set (LB3 := (pnn3, N3, 24) :: (pn3, An3, 20) :: (pnn2, N2, 24) :: (pn2, An2, 23) :: (pnn1, N1, 24) :: (pd1, D1, 32) :: (pn1, An1, 24) :: LBall) in *. set (L3 := (pnn3, 24) :: (pn3, 20) :: (pnn2, 24) :: (pn2, 23) :: (pnn1, 24) :: (pd1, 32) :: (pn1, 24) :: L) in *.
  pose proof CSTc3 as (HPc3 & _ & (errc3 & _ & _ & STc3 & _ & _ & MIc3 & _) & _). rewrite unsigned_lit in STc3 by (clear - SPR SP0; lia).
  pose proof FRMc3 as (CFRc3 & _). rewrite unsigned_lit in CFRc3 by (clear - SPR SP0; lia).
  destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CSTc3) as [NDL3 _]. subst LB3. cbn [map blk_id fst] in NDL3.
  pose proof (cstate_fresh_ids st3 [(pnn3, N3, 24); (pn3, An3, 20); (pnn2, N2, 24); (pn2, An2, 23); (pnn1, N1, 24); (pd1, D1, 32); (pn1, An1, 24)] LBall LB L _ m6 _ _ _ _ CSTc3 CO) as FRa.
  pose proof (fun q (Hq : orig LBall L q) => FRa (pnn3, N3, 24) (or_introl eq_refl) q Hq) as Fpnn3. cbn [blk_id fst] in Fpnn3.
  clear FRa.
  pose proof (nd_neq _ 5 0 _ _ NDL3 eq_refl eq_refl ltac:(discriminate)) as Npd1pnn3.
  set (LB3 := (pnn3, N3, 24) :: (pn3, An3, 20) :: (pnn2, N2, 24) :: (pn2, An2, 23) :: (pnn1, N1, 24) :: (pd1, D1, 32) :: (pn1, An1, 24) :: LBall) in *.
  assert (INS_3 : In (ps, S, 48) LB3) by (do 7 right; exact INS). assert (INK_3 : In (pk, LK, 40) LB3) by (do 7 right; exact INK).
  assert (INQ1_3 : In (pq1, Q1, 56) LB3) by (do 7 right; exact INQ1). assert (INQ2_3 : In (pq2, Q2, 56) LB3) by (do 7 right; exact INQ2).
  assert (IND_3 : In (pd1, D1, 32) LB3) by (do 5 right; left; reflexivity).
  assert (FRMo3 : cframe (ppk_T (PPK ps pk pl1 pb1 pl2 pb2 pq1 pq2 S LK lh1 B1 lh2 B2 Q1 Q2)) [] (bv_unsigned sp) s LBall L m st3 LB3 L3 m6).
  { eapply cframe_call; [exact FRMs2| exact FRMc3| rewrite unsigned_lit by (clear - SPR SP0; lia); clear; lia| intros a X; exact X|].
    intros q Hq NT. unfold pstr_T, plh_T. cbn [map concat nb16 app In]. or_cases ltac:(fun E => ht_leaf q Hq NT E). }
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFRc3 FRs2 ltac:(clear; lia)) as FRc3.
  assert (CELLc3 := cfr_cells_static _ _ _ _ _ _ _ _ CFRc3 CELLs2). cbn [cells_size csize Nat.add] in CELLc3. unfold CTX_A in CELLc3.
  specialize (CELLc3 ltac:(clear; lia) ltac:(clear; lia) ltac:(intros a Ha; unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP, LX_FLAGS; cbn [rin_ivs fst snd]; clear - Ha; lia)).
  assert (REPoc3 : plh_rep m6 LB3 L3 lh2 pl2 pb2 B2 0 (nb16 [] [] [] [] [])).
  { eapply plh_rep_cframe; [exact REPos2| exact FRMc3|]. unfold pstr_T, plh_T. cbn [map concat nb16 app In]. intros q [<-|[<-|[]]]; or_cases ltac:(fun E => pneE E). }
  assert (QCoc3 := cfr_cells_block _ _ _ _ _ _ _ _ (pq2, Q2, 56) CFRc3 QCos2 INQ2_2). unfold blk_id, blk_addr, blk_size, sk_cells in QCoc3. cbn [fst snd cells_size csize Nat.add] in QCoc3.
  specialize (QCoc3 ltac:(unfold pstr_T, plh_T; cbn [map concat nb16 app In]; or_cases ltac:(fun E => pneE E)) ltac:(clear; lia) ltac:(clear; lia)).
  clear FRs2 CELLs2 CSTs2 REPos2 QCos2 FRMc3 CFRc3 FRMs2.
  (* [comment removed for export] *)
  eapply climpl_evt. { eapply (ppi_seg3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m6 lo); [exact STc3| clear - LO Sg0 SC48; lia| clear - SLO; lia| clear - SP0; lia| exact MIc3]. }
  cbv beta. intros ms4 (m7 & -> & MU3 & WM3 & MIs3 & STs3).
  assert (CSTs3 : cstate st3 LB3 LB L3 m7 (Z_to_bv 64 (bv_unsigned sp + -48)) tp lo Bd).
  { eapply (cstate_seg _ _ _ _ _ m6 m7 _ _ tp lo Bd (bv_unsigned sp + -48)); [exact CSTc3| exact MU3| exact WM3| exact MIs3| | clear - SPR SLO LO GLO; lia| clear - SPB SP0; lia| | rewrite unsigned_lit by (clear - SPR SP0; lia); exact STs3| rewrite unsigned_lit by (clear - SPR SP0; lia); clear - SPB SPR SP0; lia].
    - constructor; [apply cwin_stack; clear - SPR SLO LO GLO; lia| constructor].
    - cbn [disjoint_from]. unfold LX_FLAGS. clear - SPR GLO SLO. lia. }
  assert (FRMs3 : cframe (ppk_T (PPK ps pk pl1 pb1 pl2 pb2 pq1 pq2 S LK lh1 B1 lh2 B2 Q1 Q2)) [] (bv_unsigned sp) s LBall L m st3 LB3 L3 m7).
  { eapply cframe_seg; [exact FRMo3| exact MU3| exact WM3| exact HPc3| clear - LO SLO SPR GLO; lia|]. constructor; [apply cseg_ok_stack; clear - LO SLO SPR GLO; lia| constructor]. }
  assert (FRs3 : rw_cells usegs m7 (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { eapply rw_cells_transport; [exact FRc3| exact MU3| exact WM3|]. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. clear - SPR SP0. lia. }
  assert (CELLs3 : rw_cells usegs m7 (CTX_A + 168) [C8 (Z_to_bv 64 S)]).
  { eapply rw_cells_transport; [exact CELLc3| exact MU3| exact WM3|]. unfold CTX_A. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. clear - SLO GLO. lia. }
  assert (SCSs3 : rw_cells usegs m7 S (psd_cells LK lh1 lh2 3 0 Q1 Q2)).
  { eapply rw_cells_transport; [exact SCSc3| exact MU3| exact WM3|]. unfold psd_cells. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. clear - SLO LO SC48. lia. }
  assert (LKCs3 : rw_cells usegs m7 LK (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))).
  { eapply rw_cells_transport; [exact LKCc3| exact MU3| exact WM3|]. unfold mutex_cells. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. clear - SLO LO LKC40. lia. }
  assert (QCs3 : rw_cells usegs m7 Q1 (sk_cells (Z_to_bv 64 3) (Z_to_bv 64 0) (Z_to_bv 64 D1) (Z_to_bv 64 0) (Z_to_bv 64 4) (Z_to_bv 64 0) (Z_to_bv 64 PROP_SK_CMPT) (Z_to_bv 64 PROP_SK_FREET) (Z_to_bv 64 PROP_SK_COPYT))).
  { eapply rw_cells_transport; [exact QCc3| exact MU3| exact WM3|]. unfold sk_cells. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. clear - SLO LO Q1C. lia. }
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CSTc3 IND_3) as (Dg0_3 & _ & _ & DCg_3 & _).
  assert (DCs3 : rw_cells usegs m7 D1 [CB 32%nat jk3]).
  { eapply rw_cells_transport; [exact DCc3| exact MU3| exact WM3|]. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. clear - SLO LO DCg_3. lia. }
  assert (REPs3 : plh_rep m7 LB3 L3 lh1 pl1 pb1 B1 3 (nb16 [] [(pnn1, N1, H_PROVIDER); (pnn2, N2, H_VERSION)] [] [] [(pnn3, N3, H_FIPS)])).
  { eapply plh_rep_munch; [exact REPc3| exact MU3| exact WM3|]. intros a Ha. cbn [outside]. clear - Ha LO SLO. lia. }
  assert (REPos3 : plh_rep m7 LB3 L3 lh2 pl2 pb2 B2 0 (nb16 [] [] [] [] [])).
  { eapply plh_rep_munch; [exact REPoc3| exact MU3| exact WM3|]. intros a Ha. cbn [outside]. clear - Ha LO SLO. lia. }
  assert (QCos3 : rw_cells usegs m7 Q2 (sk_cells (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 PROP_SK_CMPT) (Z_to_bv 64 PROP_SK_FREET) (Z_to_bv 64 PROP_SK_COPYT))).
  { eapply rw_cells_transport; [exact QCoc3| exact MU3| exact WM3|]. unfold sk_cells. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. clear - SLO LO Q2C. lia. }
  clear FRc3 CELLc3 SCSc3 LKCc3 CSTc3 FRMo3 HPc3 STc3 MIc3 MU3 WM3 QCc3 DCc3 REPc3 REPoc3 QCoc3.
  (* [comment removed for export] *)
  clear ROB NONUL NE PAD SLOW SHIGH LEN. pose proof lit_output as (ROB & NONUL & NE & PAD & SLOW & SHIGH & LEN).
  eapply climpl_seq.
  { eapply (pstr_room_true CM PUSHR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m7 st3 LB3 LB L3 f3 lo Bd CTX_A S LK lh1 lh2 3 0 Q1 Q2 A_OUTPUT s_output k_output ps pk pq1 pd1 pl1 pb1 B1 3 (nb16 [] [(pnn1, N1, H_PROVIDER); (pnn2, N2, H_VERSION)] [] [] [(pnn3, N3, H_FIPS)]) D1 3 4 0);
      [clear - Hf FU1 FU2 FU3; lia| | exact CSTs3| rewrite unsigned_lit by (clear - SPR SP0; lia); unfold PSTR_STACK, SK_PUSH_GROW_STACK, CRE_STACK, RREALLOC_STACK, RMALLOC_STACK; clear - SLO; lia
      | reflexivity| reflexivity| reflexivity| reflexivity| unfold CTX_A; clear; lia| unfold CTX_A; clear; lia| exact CELLs3| unfold CTX_A; clear; lia
      | rewrite unsigned_lit by (clear - SPR SP0; lia); clear - SP16; lia
      | exact INS_3| exact SCSs3| clear; lia| clear; lia| clear; lia| clear; lia| exact INK_3| exact LKCs3| exact REPs3| clear; lia
      | rewrite hash_output; cbn; repeat (constructor; [discriminate|]); constructor
      | exact INQ1_3| exact QCs3| clear; lia| clear; lia| clear; lia| clear; lia| exact IND_3| exact DCs3
      | exact ROB| exact NONUL| exact NE| exact PAD| exact SLOW| exact SHIGH| exact LEN
      | unfold plh_T; cbn [map concat nb16 app In]; or_cases ltac:(fun E => pneE E)| unfold plh_T; cbn [map concat nb16 app In]; or_cases ltac:(fun E => pneE E)| unfold plh_T; cbn [map concat nb16 app In]; or_cases ltac:(fun E => pneE E)| unfold plh_T; cbn [map concat nb16 app In]; or_cases ltac:(fun E => pneE E)
      | pne| pne| pne| pne| pne| pne].
    eapply croom_weaken; [eapply croom_grow; [exact ROOM| exact GA3]| | |]; wnorm; clear; lia. }
  cbv beta. intros f4 L4r st4 msr4 (v4 & m8 & LB4r & RET4 & FU4 & GR4 & CSTc4 & FRMc4 & RES).
  destruct RES as (pn4 & An4 & pnn4 & N4 & jk4 & RES). cbv zeta in RES. rewrite hash_output in RES.
  destruct RES as (-> & -> & -> & RA4 & RN4 & SCSc4 & LKCc4 & REPc4 & QCc4 & DCc4 & _).
  destruct RET4 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->). cret_lit.
  wnormH GR4. pose proof (cgrow_trans _ _ _ _ _ _ _ _ _ GA3 GR4) as GA4. clear GR4.
  (* [comment removed for export] *)
  change (Z.of_nat (length s_output) + 16) with 22 in *. change (cnt_of true 3 0 + 1) with 4 in *. cbn [ni_after vi_after t_of q_of] in SCSc4, REPc4, QCc4.
  change (3 + 1) with 4 in REPc4.
  change (lupd (Z.to_nat (H_OUTPUT mod 8)) (nth (Z.to_nat (H_OUTPUT mod 8)) (nb16 [] [(pnn1, N1, H_PROVIDER); (pnn2, N2, H_VERSION)] [] [] [(pnn3, N3, H_FIPS)]) [] ++ [(pnn4, N4, H_OUTPUT)]) (nb16 [] [(pnn1, N1, H_PROVIDER); (pnn2, N2, H_VERSION)] [] [] [(pnn3, N3, H_FIPS)])) with (nb16 [(pnn4, N4, H_OUTPUT)] [(pnn1, N1, H_PROVIDER); (pnn2, N2, H_VERSION)] [] [] [(pnn3, N3, H_FIPS)]) in REPc4.
  set (LB4 := (pnn4, N4, 24) :: (pn4, An4, 22) :: (pnn3, N3, 24) :: (pn3, An3, 20) :: (pnn2, N2, 24) :: (pn2, An2, 23) :: (pnn1, N1, 24) :: (pd1, D1, 32) :: (pn1, An1, 24) :: LBall) in *. set (L4 := (pnn4, 24) :: (pn4, 22) :: (pnn3, 24) :: (pn3, 20) :: (pnn2, 24) :: (pn2, 23) :: (pnn1, 24) :: (pd1, 32) :: (pn1, 24) :: L) in *.
  pose proof CSTc4 as (HPc4 & _ & (errc4 & _ & _ & STc4 & _ & _ & MIc4 & _) & _). rewrite unsigned_lit in STc4 by (clear - SPR SP0; lia).
  pose proof FRMc4 as (CFRc4 & _). rewrite unsigned_lit in CFRc4 by (clear - SPR SP0; lia).
  destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CSTc4) as [NDL4 _]. subst LB4. cbn [map blk_id fst] in NDL4.
  pose proof (cstate_fresh_ids st4 [(pnn4, N4, 24); (pn4, An4, 22); (pnn3, N3, 24); (pn3, An3, 20); (pnn2, N2, 24); (pn2, An2, 23); (pnn1, N1, 24); (pd1, D1, 32); (pn1, An1, 24)] LBall LB L _ m8 _ _ _ _ CSTc4 CO) as FRa.
  pose proof (fun q (Hq : orig LBall L q) => FRa (pnn4, N4, 24) (or_introl eq_refl) q Hq) as Fpnn4. cbn [blk_id fst] in Fpnn4.
  clear FRa.
  pose proof (nd_neq _ 7 0 _ _ NDL4 eq_refl eq_refl ltac:(discriminate)) as Npd1pnn4.
  set (LB4 := (pnn4, N4, 24) :: (pn4, An4, 22) :: (pnn3, N3, 24) :: (pn3, An3, 20) :: (pnn2, N2, 24) :: (pn2, An2, 23) :: (pnn1, N1, 24) :: (pd1, D1, 32) :: (pn1, An1, 24) :: LBall) in *.
  assert (INS_4 : In (ps, S, 48) LB4) by (do 9 right; exact INS). assert (INK_4 : In (pk, LK, 40) LB4) by (do 9 right; exact INK).
  assert (INQ1_4 : In (pq1, Q1, 56) LB4) by (do 9 right; exact INQ1). assert (INQ2_4 : In (pq2, Q2, 56) LB4) by (do 9 right; exact INQ2).
  assert (IND_4 : In (pd1, D1, 32) LB4) by (do 7 right; left; reflexivity).
  assert (FRMo4 : cframe (ppk_T (PPK ps pk pl1 pb1 pl2 pb2 pq1 pq2 S LK lh1 B1 lh2 B2 Q1 Q2)) [] (bv_unsigned sp) s LBall L m st4 LB4 L4 m8).
  { eapply cframe_call; [exact FRMs3| exact FRMc4| rewrite unsigned_lit by (clear - SPR SP0; lia); clear; lia| intros a X; exact X|].
    intros q Hq NT. unfold pstr_T, plh_T. cbn [map concat nb16 app In]. or_cases ltac:(fun E => ht_leaf q Hq NT E). }
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFRc4 FRs3 ltac:(clear; lia)) as FRc4.
  assert (CELLc4 := cfr_cells_static _ _ _ _ _ _ _ _ CFRc4 CELLs3). cbn [cells_size csize Nat.add] in CELLc4. unfold CTX_A in CELLc4.
  specialize (CELLc4 ltac:(clear; lia) ltac:(clear; lia) ltac:(intros a Ha; unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP, LX_FLAGS; cbn [rin_ivs fst snd]; clear - Ha; lia)).
  assert (REPoc4 : plh_rep m8 LB4 L4 lh2 pl2 pb2 B2 0 (nb16 [] [] [] [] [])).
  { eapply plh_rep_cframe; [exact REPos3| exact FRMc4|]. unfold pstr_T, plh_T. cbn [map concat nb16 app In]. intros q [<-|[<-|[]]]; or_cases ltac:(fun E => pneE E). }
  assert (QCoc4 := cfr_cells_block _ _ _ _ _ _ _ _ (pq2, Q2, 56) CFRc4 QCos3 INQ2_3). unfold blk_id, blk_addr, blk_size, sk_cells in QCoc4. cbn [fst snd cells_size csize Nat.add] in QCoc4.
  specialize (QCoc4 ltac:(unfold pstr_T, plh_T; cbn [map concat nb16 app In]; or_cases ltac:(fun E => pneE E)) ltac:(clear; lia) ltac:(clear; lia)).
  clear FRs3 CELLs3 CSTs3 REPos3 QCos3 FRMc4 CFRc4 FRMs3.
  (* [comment removed for export] *)
  eapply climpl_evt. { eapply (ppi_seg4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m8 lo); [exact STc4| clear - LO Sg0 SC48; lia| clear - SLO; lia| clear - SP0; lia| exact MIc4]. }
  cbv beta. intros ms5 (m9 & -> & MU4 & WM4 & MIs4 & STs4).
  assert (CSTs4 : cstate st4 LB4 LB L4 m9 (Z_to_bv 64 (bv_unsigned sp + -48)) tp lo Bd).
  { eapply (cstate_seg _ _ _ _ _ m8 m9 _ _ tp lo Bd (bv_unsigned sp + -48)); [exact CSTc4| exact MU4| exact WM4| exact MIs4| | clear - SPR SLO LO GLO; lia| clear - SPB SP0; lia| | rewrite unsigned_lit by (clear - SPR SP0; lia); exact STs4| rewrite unsigned_lit by (clear - SPR SP0; lia); clear - SPB SPR SP0; lia].
    - constructor; [apply cwin_stack; clear - SPR SLO LO GLO; lia| constructor].
    - cbn [disjoint_from]. unfold LX_FLAGS. clear - SPR GLO SLO. lia. }
  assert (FRMs4 : cframe (ppk_T (PPK ps pk pl1 pb1 pl2 pb2 pq1 pq2 S LK lh1 B1 lh2 B2 Q1 Q2)) [] (bv_unsigned sp) s LBall L m st4 LB4 L4 m9).
  { eapply cframe_seg; [exact FRMo4| exact MU4| exact WM4| exact HPc4| clear - LO SLO SPR GLO; lia|]. constructor; [apply cseg_ok_stack; clear - LO SLO SPR GLO; lia| constructor]. }
  assert (FRs4 : rw_cells usegs m9 (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { eapply rw_cells_transport; [exact FRc4| exact MU4| exact WM4|]. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. clear - SPR SP0. lia. }
  assert (CELLs4 : rw_cells usegs m9 (CTX_A + 168) [C8 (Z_to_bv 64 S)]).
  { eapply rw_cells_transport; [exact CELLc4| exact MU4| exact WM4|]. unfold CTX_A. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. clear - SLO GLO. lia. }
  assert (SCSs4 : rw_cells usegs m9 S (psd_cells LK lh1 lh2 4 0 Q1 Q2)).
  { eapply rw_cells_transport; [exact SCSc4| exact MU4| exact WM4|]. unfold psd_cells. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. clear - SLO LO SC48. lia. }
  assert (LKCs4 : rw_cells usegs m9 LK (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))).
  { eapply rw_cells_transport; [exact LKCc4| exact MU4| exact WM4|]. unfold mutex_cells. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. clear - SLO LO LKC40. lia. }
  assert (QCs4 : rw_cells usegs m9 Q1 (sk_cells (Z_to_bv 64 4) (Z_to_bv 64 0) (Z_to_bv 64 D1) (Z_to_bv 64 0) (Z_to_bv 64 4) (Z_to_bv 64 0) (Z_to_bv 64 PROP_SK_CMPT) (Z_to_bv 64 PROP_SK_FREET) (Z_to_bv 64 PROP_SK_COPYT))).
  { eapply rw_cells_transport; [exact QCc4| exact MU4| exact WM4|]. unfold sk_cells. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. clear - SLO LO Q1C. lia. }
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CSTc4 IND_4) as (Dg0_4 & _ & _ & DCg_4 & _).
  assert (DCs4 : rw_cells usegs m9 D1 [CB 32%nat jk4]).
  { eapply rw_cells_transport; [exact DCc4| exact MU4| exact WM4|]. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. clear - SLO LO DCg_4. lia. }
  assert (REPs4 : plh_rep m9 LB4 L4 lh1 pl1 pb1 B1 4 (nb16 [(pnn4, N4, H_OUTPUT)] [(pnn1, N1, H_PROVIDER); (pnn2, N2, H_VERSION)] [] [] [(pnn3, N3, H_FIPS)])).
  { eapply plh_rep_munch; [exact REPc4| exact MU4| exact WM4|]. intros a Ha. cbn [outside]. clear - Ha LO SLO. lia. }
  assert (REPos4 : plh_rep m9 LB4 L4 lh2 pl2 pb2 B2 0 (nb16 [] [] [] [] [])).
  { eapply plh_rep_munch; [exact REPoc4| exact MU4| exact WM4|]. intros a Ha. cbn [outside]. clear - Ha LO SLO. lia. }
  assert (QCos4 : rw_cells usegs m9 Q2 (sk_cells (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 PROP_SK_CMPT) (Z_to_bv 64 PROP_SK_FREET) (Z_to_bv 64 PROP_SK_COPYT))).
  { eapply rw_cells_transport; [exact QCoc4| exact MU4| exact WM4|]. unfold sk_cells. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. clear - SLO LO Q2C. lia. }
  clear FRc4 CELLc4 SCSc4 LKCc4 CSTc4 FRMo4 HPc4 STc4 MIc4 MU4 WM4 QCc4 DCc4 REPc4 REPoc4 QCoc4.
  (* [comment removed for export] *)
  clear ROB NONUL NE PAD SLOW SHIGH LEN. pose proof lit_input as (ROB & NONUL & NE & PAD & SLOW & SHIGH & LEN).
  assert (OWND : cown LB4 L4 pd1 D1 32 32) by (split; [exact IND_4| subst L4; do 7 right; left; reflexivity]).
  eapply climpl_seq.
  { eapply (pstr_grow_true CM PUSHG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m9 st4 LB4 LB L4 f4 lo Bd CTX_A S LK lh1 lh2 4 0 Q1 Q2 A_INPUT s_input k_input ps pk pq1 pd1 pl1 pb1 B1 4 (nb16 [(pnn4, N4, H_OUTPUT)] [(pnn1, N1, H_PROVIDER); (pnn2, N2, H_VERSION)] [] [] [(pnn3, N3, H_FIPS)]) D1);
      [clear - Hf FU1 FU2 FU3 FU4; lia| | exact CSTs4| rewrite unsigned_lit by (clear - SPR SP0; lia); unfold PSTR_STACK, SK_PUSH_GROW_STACK, CRE_STACK, RREALLOC_STACK, RMALLOC_STACK; clear - SLO; lia
      | reflexivity| reflexivity| reflexivity| reflexivity| unfold CTX_A; clear; lia| unfold CTX_A; clear; lia| exact CELLs4| unfold CTX_A; clear; lia
      | rewrite unsigned_lit by (clear - SPR SP0; lia); clear - SP16; lia
      | exact INS_4| exact SCSs4| clear; lia| clear; lia| clear; lia| clear; lia| exact INK_4| exact LKCs4| exact REPs4| clear; lia
      | rewrite hash_input; cbn; repeat (constructor; [discriminate|]); constructor
      | exact INQ1_4| exact QCs4| exact OWND| exact DCs4
      | exact ROB| exact NONUL| exact NE| exact PAD| exact SLOW| exact SHIGH| exact LEN
      | unfold plh_T; cbn [map concat nb16 app In]; or_cases ltac:(fun E => pneE E)| unfold plh_T; cbn [map concat nb16 app In]; or_cases ltac:(fun E => pneE E)| unfold plh_T; cbn [map concat nb16 app In]; or_cases ltac:(fun E => pneE E)| unfold plh_T; cbn [map concat nb16 app In]; or_cases ltac:(fun E => pneE E)
      | pne| pne| pne| pne| pne| pne].
    eapply croom_weaken; [eapply croom_grow; [exact ROOM| exact GA4]| | |]; wnorm; clear; lia. }
  cbv beta. intros f5 L5r st5 msr5 (v5 & m10 & LB5r & RET5 & FU5 & GR5 & CSTc5 & FRMc5 & RES).
  destruct RES as (pn5 & An5 & q5 & E5 & pnn5 & N5 & L3_5 & jk5 & RES). cbv zeta in RES. rewrite hash_input in RES.
  destruct RES as (-> & -> & -> & ALT5 & RA5 & RE5 & RN5 & SCSc5 & LKCc5 & REPc5 & QCc5 & DCc5 & _).
  destruct RET5 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->). cret_lit.
  wnormH GR5. pose proof (cgrow_trans _ _ _ _ _ _ _ _ _ GA4 GR5) as GA5. clear GR5.
  (* [comment removed for export] *)
  change (Z.of_nat (length s_input) + 16) with 21 in *. change (cnt_of true 4 0 + 1) with 5 in *. cbn [ni_after vi_after t_of q_of] in SCSc5, REPc5, QCc5.
  change (4 + 1) with 5 in REPc5.
  change (lupd (Z.to_nat (H_INPUT mod 8)) (nth (Z.to_nat (H_INPUT mod 8)) (nb16 [(pnn4, N4, H_OUTPUT)] [(pnn1, N1, H_PROVIDER); (pnn2, N2, H_VERSION)] [] [] [(pnn3, N3, H_FIPS)]) [] ++ [(pnn5, N5, H_INPUT)]) (nb16 [(pnn4, N4, H_OUTPUT)] [(pnn1, N1, H_PROVIDER); (pnn2, N2, H_VERSION)] [] [] [(pnn3, N3, H_FIPS)])) with (nb16 [(pnn4, N4, H_OUTPUT)] [(pnn1, N1, H_PROVIDER); (pnn2, N2, H_VERSION); (pnn5, N5, H_INPUT)] [] [] [(pnn3, N3, H_FIPS)]) in REPc5.
  assert (RM : lb_remove pd1 LB4 = (pnn4, N4, 24) :: (pn4, An4, 22) :: (pnn3, N3, 24) :: (pn3, An3, 20) :: (pnn2, N2, 24) :: (pn2, An2, 23) :: (pnn1, N1, 24) :: (pn1, An1, 24) :: LBall) by (subst LB4; apply (lb_remove_prefix [(pnn4, N4, 24); (pn4, An4, 22); (pnn3, N3, 24); (pn3, An3, 20); (pnn2, N2, 24); (pn2, An2, 23); (pnn1, N1, 24)] (pd1, D1, 32) [(pn1, An1, 24)] LBall); [reflexivity| exact NDL4]).
  rewrite RM in *. clear RM.
  set (LB5 := (pnn5, N5, 24) :: (q5, E5, 48) :: (pn5, An5, 21) :: (pnn4, N4, 24) :: (pn4, An4, 22) :: (pnn3, N3, 24) :: (pn3, An3, 20) :: (pnn2, N2, 24) :: (pn2, An2, 23) :: (pnn1, N1, 24) :: (pn1, An1, 24) :: LBall) in *.
  set (L5 := (pnn5, 24) :: L3_5) in *.
  pose proof CSTc5 as (HPc5 & _ & (errc5 & _ & _ & STc5 & _ & _ & MIc5 & _) & _). rewrite unsigned_lit in STc5 by (clear - SPR SP0; lia).
  pose proof FRMc5 as (CFRc5 & _). rewrite unsigned_lit in CFRc5 by (clear - SPR SP0; lia).
  destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CSTc5) as [NDL5 _]. subst LB5. cbn [map blk_id fst] in NDL5.
  pose proof (cstate_fresh_ids st5 [(pnn5, N5, 24); (q5, E5, 48); (pn5, An5, 21); (pnn4, N4, 24); (pn4, An4, 22); (pnn3, N3, 24); (pn3, An3, 20); (pnn2, N2, 24); (pn2, An2, 23); (pnn1, N1, 24); (pn1, An1, 24)] LBall LB L _ m10 _ _ _ _ CSTc5 CO) as FRa.
  pose proof (fun q (Hq : orig LBall L q) => FRa (pnn5, N5, 24) (or_introl eq_refl) q Hq) as Fpnn5. cbn [blk_id fst] in Fpnn5.
  pose proof (fun q (Hq : orig LBall L q) => FRa (q5, E5, 48) (or_intror (or_introl eq_refl)) q Hq) as Fq5. cbn [blk_id fst] in Fq5.
  clear FRa.
  pose proof (nd_neq _ 1 3 _ _ NDL5 eq_refl eq_refl ltac:(discriminate)) as Nq5pnn4.
  pose proof (nd_neq _ 1 9 _ _ NDL5 eq_refl eq_refl ltac:(discriminate)) as Nq5pnn1.
  pose proof (nd_neq _ 1 7 _ _ NDL5 eq_refl eq_refl ltac:(discriminate)) as Nq5pnn2.
  pose proof (nd_neq _ 1 0 _ _ NDL5 eq_refl eq_refl ltac:(discriminate)) as Nq5pnn5.
  pose proof (nd_neq _ 1 5 _ _ NDL5 eq_refl eq_refl ltac:(discriminate)) as Nq5pnn3.
  set (LB5 := (pnn5, N5, 24) :: (q5, E5, 48) :: (pn5, An5, 21) :: (pnn4, N4, 24) :: (pn4, An4, 22) :: (pnn3, N3, 24) :: (pn3, An3, 20) :: (pnn2, N2, 24) :: (pn2, An2, 23) :: (pnn1, N1, 24) :: (pn1, An1, 24) :: LBall) in *.
  assert (INS_5 : In (ps, S, 48) LB5) by (do 11 right; exact INS). assert (INK_5 : In (pk, LK, 40) LB5) by (do 11 right; exact INK).
  assert (INQ1_5 : In (pq1, Q1, 56) LB5) by (do 11 right; exact INQ1). assert (INQ2_5 : In (pq2, Q2, 56) LB5) by (do 11 right; exact INQ2).
  assert (IND_5 : In (q5, E5, 48) LB5) by (do 1 right; left; reflexivity).
  assert (FRMo5 : cframe (ppk_T (PPK ps pk pl1 pb1 pl2 pb2 pq1 pq2 S LK lh1 B1 lh2 B2 Q1 Q2)) [] (bv_unsigned sp) s LBall L m st5 LB5 L5 m10).
  { eapply cframe_call; [exact FRMs4| exact FRMc5| rewrite unsigned_lit by (clear - SPR SP0; lia); clear; lia| intros a X; exact X|].
    intros q Hq NT. unfold pstr_T, plh_T. cbn [map concat nb16 app In]. or_cases ltac:(fun E => ht_leaf q Hq NT E). }
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFRc5 FRs4 ltac:(clear; lia)) as FRc5.
  assert (CELLc5 := cfr_cells_static _ _ _ _ _ _ _ _ CFRc5 CELLs4). cbn [cells_size csize Nat.add] in CELLc5. unfold CTX_A in CELLc5.
  specialize (CELLc5 ltac:(clear; lia) ltac:(clear; lia) ltac:(intros a Ha; unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP, LX_FLAGS; cbn [rin_ivs fst snd]; clear - Ha; lia)).
  assert (REPoc5 : plh_rep m10 LB5 L5 lh2 pl2 pb2 B2 0 (nb16 [] [] [] [] [])).
  { eapply plh_rep_cframe; [exact REPos4| exact FRMc5|]. unfold pstr_T, plh_T. cbn [map concat nb16 app In]. intros q [<-|[<-|[]]]; or_cases ltac:(fun E => pneE E). }
  assert (QCoc5 := cfr_cells_block _ _ _ _ _ _ _ _ (pq2, Q2, 56) CFRc5 QCos4 INQ2_4). unfold blk_id, blk_addr, blk_size, sk_cells in QCoc5. cbn [fst snd cells_size csize Nat.add] in QCoc5.
  specialize (QCoc5 ltac:(unfold pstr_T, plh_T; cbn [map concat nb16 app In]; or_cases ltac:(fun E => pneE E)) ltac:(clear; lia) ltac:(clear; lia)).
  clear FRs4 CELLs4 CSTs4 REPos4 QCos4 FRMc5 CFRc5 FRMs4.
  (* [comment removed for export] *)
  eapply climpl_evt. { eapply (ppi_seg5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m10 lo); [exact STc5| clear - LO Sg0 SC48; lia| clear - SLO; lia| clear - SP0; lia| exact MIc5]. }
  cbv beta. intros ms6 (m11 & -> & MU5 & WM5 & MIs5 & STs5).
  assert (CSTs5 : cstate st5 LB5 LB L5 m11 (Z_to_bv 64 (bv_unsigned sp + -48)) tp lo Bd).
  { eapply (cstate_seg _ _ _ _ _ m10 m11 _ _ tp lo Bd (bv_unsigned sp + -48)); [exact CSTc5| exact MU5| exact WM5| exact MIs5| | clear - SPR SLO LO GLO; lia| clear - SPB SP0; lia| | rewrite unsigned_lit by (clear - SPR SP0; lia); exact STs5| rewrite unsigned_lit by (clear - SPR SP0; lia); clear - SPB SPR SP0; lia].
    - constructor; [apply cwin_stack; clear - SPR SLO LO GLO; lia| constructor].
    - cbn [disjoint_from]. unfold LX_FLAGS. clear - SPR GLO SLO. lia. }
  assert (FRMs5 : cframe (ppk_T (PPK ps pk pl1 pb1 pl2 pb2 pq1 pq2 S LK lh1 B1 lh2 B2 Q1 Q2)) [] (bv_unsigned sp) s LBall L m st5 LB5 L5 m11).
  { eapply cframe_seg; [exact FRMo5| exact MU5| exact WM5| exact HPc5| clear - LO SLO SPR GLO; lia|]. constructor; [apply cseg_ok_stack; clear - LO SLO SPR GLO; lia| constructor]. }
  assert (FRs5 : rw_cells usegs m11 (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { eapply rw_cells_transport; [exact FRc5| exact MU5| exact WM5|]. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. clear - SPR SP0. lia. }
  assert (CELLs5 : rw_cells usegs m11 (CTX_A + 168) [C8 (Z_to_bv 64 S)]).
  { eapply rw_cells_transport; [exact CELLc5| exact MU5| exact WM5|]. unfold CTX_A. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. clear - SLO GLO. lia. }
  assert (SCSs5 : rw_cells usegs m11 S (psd_cells LK lh1 lh2 5 0 Q1 Q2)).
  { eapply rw_cells_transport; [exact SCSc5| exact MU5| exact WM5|]. unfold psd_cells. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. clear - SLO LO SC48. lia. }
  assert (LKCs5 : rw_cells usegs m11 LK (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))).
  { eapply rw_cells_transport; [exact LKCc5| exact MU5| exact WM5|]. unfold mutex_cells. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. clear - SLO LO LKC40. lia. }
  assert (QCs5 : rw_cells usegs m11 Q1 (sk_cells (Z_to_bv 64 5) (Z_to_bv 64 0) (Z_to_bv 64 E5) (Z_to_bv 64 0) (Z_to_bv 64 6) (Z_to_bv 64 0) (Z_to_bv 64 PROP_SK_CMPT) (Z_to_bv 64 PROP_SK_FREET) (Z_to_bv 64 PROP_SK_COPYT))).
  { eapply rw_cells_transport; [exact QCc5| exact MU5| exact WM5|]. unfold sk_cells. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. clear - SLO LO Q1C. lia. }
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CSTc5 IND_5) as (Dg0_5 & _ & _ & DCg_5 & _).
  assert (DCs5 : rw_cells usegs m11 E5 [CB 48%nat jk5]).
  { eapply rw_cells_transport; [exact DCc5| exact MU5| exact WM5|]. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. clear - SLO LO DCg_5. lia. }
  assert (REPs5 : plh_rep m11 LB5 L5 lh1 pl1 pb1 B1 5 (nb16 [(pnn4, N4, H_OUTPUT)] [(pnn1, N1, H_PROVIDER); (pnn2, N2, H_VERSION); (pnn5, N5, H_INPUT)] [] [] [(pnn3, N3, H_FIPS)])).
  { eapply plh_rep_munch; [exact REPc5| exact MU5| exact WM5|]. intros a Ha. cbn [outside]. clear - Ha LO SLO. lia. }
  assert (REPos5 : plh_rep m11 LB5 L5 lh2 pl2 pb2 B2 0 (nb16 [] [] [] [] [])).
  { eapply plh_rep_munch; [exact REPoc5| exact MU5| exact WM5|]. intros a Ha. cbn [outside]. clear - Ha LO SLO. lia. }
  assert (QCos5 : rw_cells usegs m11 Q2 (sk_cells (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 PROP_SK_CMPT) (Z_to_bv 64 PROP_SK_FREET) (Z_to_bv 64 PROP_SK_COPYT))).
  { eapply rw_cells_transport; [exact QCoc5| exact MU5| exact WM5|]. unfold sk_cells. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. clear - SLO LO Q2C. lia. }
  clear FRc5 CELLc5 SCSc5 LKCc5 CSTc5 FRMo5 HPc5 STc5 MIc5 MU5 WM5 QCc5 DCc5 REPc5 REPoc5 QCoc5.
  (* [comment removed for export] *)
  clear ROB NONUL NE PAD SLOW SHIGH LEN. pose proof lit_structure as (ROB & NONUL & NE & PAD & SLOW & SHIGH & LEN).
  eapply climpl_seq.
  { eapply (pstr_room_true CM PUSHR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m11 st5 LB5 LB L5 f5 lo Bd CTX_A S LK lh1 lh2 5 0 Q1 Q2 A_STRUCTURE s_structure k_structure ps pk pq1 q5 pl1 pb1 B1 5 (nb16 [(pnn4, N4, H_OUTPUT)] [(pnn1, N1, H_PROVIDER); (pnn2, N2, H_VERSION); (pnn5, N5, H_INPUT)] [] [] [(pnn3, N3, H_FIPS)]) E5 5 6 0);
      [clear - Hf FU1 FU2 FU3 FU4 FU5; lia| | exact CSTs5| rewrite unsigned_lit by (clear - SPR SP0; lia); unfold PSTR_STACK, SK_PUSH_GROW_STACK, CRE_STACK, RREALLOC_STACK, RMALLOC_STACK; clear - SLO; lia
      | reflexivity| reflexivity| reflexivity| reflexivity| unfold CTX_A; clear; lia| unfold CTX_A; clear; lia| exact CELLs5| unfold CTX_A; clear; lia
      | rewrite unsigned_lit by (clear - SPR SP0; lia); clear - SP16; lia
      | exact INS_5| exact SCSs5| clear; lia| clear; lia| clear; lia| clear; lia| exact INK_5| exact LKCs5| exact REPs5| clear; lia
      | rewrite hash_structure; cbn; repeat (constructor; [discriminate|]); constructor
      | exact INQ1_5| exact QCs5| clear; lia| clear; lia| clear; lia| clear; lia| exact IND_5| exact DCs5
      | exact ROB| exact NONUL| exact NE| exact PAD| exact SLOW| exact SHIGH| exact LEN
      | unfold plh_T; cbn [map concat nb16 app In]; or_cases ltac:(fun E => pneE E)| unfold plh_T; cbn [map concat nb16 app In]; or_cases ltac:(fun E => pneE E)| unfold plh_T; cbn [map concat nb16 app In]; or_cases ltac:(fun E => pneE E)| unfold plh_T; cbn [map concat nb16 app In]; or_cases ltac:(fun E => pneE E)
      | pne| pne| pne| pne| pne| pne].
    eapply croom_weaken; [eapply croom_grow; [exact ROOM| exact GA5]| | |]; wnorm; clear; lia. }
  cbv beta. intros f6 L6r st6 msr6 (v6 & m12 & LB6r & RET6 & FU6 & GR6 & CSTc6 & FRMc6 & RES).
  destruct RES as (pn6 & An6 & pnn6 & N6 & jk6 & RES). cbv zeta in RES. rewrite hash_structure in RES.
  destruct RES as (-> & -> & -> & RA6 & RN6 & SCSc6 & LKCc6 & REPc6 & QCc6 & DCc6 & _).
  destruct RET6 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->). cret_lit.
  wnormH GR6. pose proof (cgrow_trans _ _ _ _ _ _ _ _ _ GA5 GR6) as GA6. clear GR6.
  (* [comment removed for export] *)
  change (Z.of_nat (length s_structure) + 16) with 25 in *. change (cnt_of true 5 0 + 1) with 6 in *. cbn [ni_after vi_after t_of q_of] in SCSc6, REPc6, QCc6.
  change (5 + 1) with 6 in REPc6.
  change (lupd (Z.to_nat (H_STRUCTURE mod 8)) (nth (Z.to_nat (H_STRUCTURE mod 8)) (nb16 [(pnn4, N4, H_OUTPUT)] [(pnn1, N1, H_PROVIDER); (pnn2, N2, H_VERSION); (pnn5, N5, H_INPUT)] [] [] [(pnn3, N3, H_FIPS)]) [] ++ [(pnn6, N6, H_STRUCTURE)]) (nb16 [(pnn4, N4, H_OUTPUT)] [(pnn1, N1, H_PROVIDER); (pnn2, N2, H_VERSION); (pnn5, N5, H_INPUT)] [] [] [(pnn3, N3, H_FIPS)])) with (nb16 [(pnn4, N4, H_OUTPUT)] [(pnn1, N1, H_PROVIDER); (pnn2, N2, H_VERSION); (pnn5, N5, H_INPUT)] [] [] [(pnn3, N3, H_FIPS); (pnn6, N6, H_STRUCTURE)]) in REPc6.
  set (LB6 := (pnn6, N6, 24) :: (pn6, An6, 25) :: (pnn5, N5, 24) :: (q5, E5, 48) :: (pn5, An5, 21) :: (pnn4, N4, 24) :: (pn4, An4, 22) :: (pnn3, N3, 24) :: (pn3, An3, 20) :: (pnn2, N2, 24) :: (pn2, An2, 23) :: (pnn1, N1, 24) :: (pn1, An1, 24) :: LBall) in *. set (L6 := (pnn6, 24) :: (pn6, 25) :: L5) in *.
  pose proof CSTc6 as (HPc6 & _ & (errc6 & _ & _ & STc6 & _ & _ & MIc6 & _) & _). rewrite unsigned_lit in STc6 by (clear - SPR SP0; lia).
  pose proof FRMc6 as (CFRc6 & _). rewrite unsigned_lit in CFRc6 by (clear - SPR SP0; lia).
  destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CSTc6) as [NDL6 _]. subst LB6. cbn [map blk_id fst] in NDL6.
  pose proof (cstate_fresh_ids st6 [(pnn6, N6, 24); (pn6, An6, 25); (pnn5, N5, 24); (q5, E5, 48); (pn5, An5, 21); (pnn4, N4, 24); (pn4, An4, 22); (pnn3, N3, 24); (pn3, An3, 20); (pnn2, N2, 24); (pn2, An2, 23); (pnn1, N1, 24); (pn1, An1, 24)] LBall LB L _ m12 _ _ _ _ CSTc6 CO) as FRa.
  pose proof (fun q (Hq : orig LBall L q) => FRa (pnn6, N6, 24) (or_introl eq_refl) q Hq) as Fpnn6. cbn [blk_id fst] in Fpnn6.
  clear FRa.
  pose proof (nd_neq _ 3 0 _ _ NDL6 eq_refl eq_refl ltac:(discriminate)) as Nq5pnn6.
  set (LB6 := (pnn6, N6, 24) :: (pn6, An6, 25) :: (pnn5, N5, 24) :: (q5, E5, 48) :: (pn5, An5, 21) :: (pnn4, N4, 24) :: (pn4, An4, 22) :: (pnn3, N3, 24) :: (pn3, An3, 20) :: (pnn2, N2, 24) :: (pn2, An2, 23) :: (pnn1, N1, 24) :: (pn1, An1, 24) :: LBall) in *.
  assert (INS_6 : In (ps, S, 48) LB6) by (do 13 right; exact INS). assert (INK_6 : In (pk, LK, 40) LB6) by (do 13 right; exact INK).
  assert (INQ1_6 : In (pq1, Q1, 56) LB6) by (do 13 right; exact INQ1). assert (INQ2_6 : In (pq2, Q2, 56) LB6) by (do 13 right; exact INQ2).
  assert (IND_6 : In (q5, E5, 48) LB6) by (do 3 right; left; reflexivity).
  assert (FRMo6 : cframe (ppk_T (PPK ps pk pl1 pb1 pl2 pb2 pq1 pq2 S LK lh1 B1 lh2 B2 Q1 Q2)) [] (bv_unsigned sp) s LBall L m st6 LB6 L6 m12).
  { eapply cframe_call; [exact FRMs5| exact FRMc6| rewrite unsigned_lit by (clear - SPR SP0; lia); clear; lia| intros a X; exact X|].
    intros q Hq NT. unfold pstr_T, plh_T. cbn [map concat nb16 app In]. or_cases ltac:(fun E => ht_leaf q Hq NT E). }
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFRc6 FRs5 ltac:(clear; lia)) as FRc6.
  assert (CELLc6 := cfr_cells_static _ _ _ _ _ _ _ _ CFRc6 CELLs5). cbn [cells_size csize Nat.add] in CELLc6. unfold CTX_A in CELLc6.
  specialize (CELLc6 ltac:(clear; lia) ltac:(clear; lia) ltac:(intros a Ha; unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP, LX_FLAGS; cbn [rin_ivs fst snd]; clear - Ha; lia)).
  assert (REPoc6 : plh_rep m12 LB6 L6 lh2 pl2 pb2 B2 0 (nb16 [] [] [] [] [])).
  { eapply plh_rep_cframe; [exact REPos5| exact FRMc6|]. unfold pstr_T, plh_T. cbn [map concat nb16 app In]. intros q [<-|[<-|[]]]; or_cases ltac:(fun E => pneE E). }
  assert (QCoc6 := cfr_cells_block _ _ _ _ _ _ _ _ (pq2, Q2, 56) CFRc6 QCos5 INQ2_5). unfold blk_id, blk_addr, blk_size, sk_cells in QCoc6. cbn [fst snd cells_size csize Nat.add] in QCoc6.
  specialize (QCoc6 ltac:(unfold pstr_T, plh_T; cbn [map concat nb16 app In]; or_cases ltac:(fun E => pneE E)) ltac:(clear; lia) ltac:(clear; lia)).
  clear FRs5 CELLs5 CSTs5 REPos5 QCos5 FRMc6 CFRc6 FRMs5.
  (* [comment removed for export] *)
  eapply climpl_evt. { eapply (ppi_seg6 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m12 lo); [exact STc6| clear - LO Sg0 SC48; lia| clear - SLO; lia| clear - SP0; lia| exact MIc6]. }
  cbv beta. intros ms7 (m13 & -> & MU6 & WM6 & MIs6 & STs6).
  assert (CSTs6 : cstate st6 LB6 LB L6 m13 (Z_to_bv 64 (bv_unsigned sp + -48)) tp lo Bd).
  { eapply (cstate_seg _ _ _ _ _ m12 m13 _ _ tp lo Bd (bv_unsigned sp + -48)); [exact CSTc6| exact MU6| exact WM6| exact MIs6| | clear - SPR SLO LO GLO; lia| clear - SPB SP0; lia| | rewrite unsigned_lit by (clear - SPR SP0; lia); exact STs6| rewrite unsigned_lit by (clear - SPR SP0; lia); clear - SPB SPR SP0; lia].
    - constructor; [apply cwin_stack; clear - SPR SLO LO GLO; lia| constructor].
    - cbn [disjoint_from]. unfold LX_FLAGS. clear - SPR GLO SLO. lia. }
  assert (FRMs6 : cframe (ppk_T (PPK ps pk pl1 pb1 pl2 pb2 pq1 pq2 S LK lh1 B1 lh2 B2 Q1 Q2)) [] (bv_unsigned sp) s LBall L m st6 LB6 L6 m13).
  { eapply cframe_seg; [exact FRMo6| exact MU6| exact WM6| exact HPc6| clear - LO SLO SPR GLO; lia|]. constructor; [apply cseg_ok_stack; clear - LO SLO SPR GLO; lia| constructor]. }
  assert (FRs6 : rw_cells usegs m13 (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { eapply rw_cells_transport; [exact FRc6| exact MU6| exact WM6|]. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. clear - SPR SP0. lia. }
  assert (CELLs6 : rw_cells usegs m13 (CTX_A + 168) [C8 (Z_to_bv 64 S)]).
  { eapply rw_cells_transport; [exact CELLc6| exact MU6| exact WM6|]. unfold CTX_A. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. clear - SLO GLO. lia. }
  assert (SCSs6 : rw_cells usegs m13 S (psd_cells LK lh1 lh2 6 0 Q1 Q2)).
  { eapply rw_cells_transport; [exact SCSc6| exact MU6| exact WM6|]. unfold psd_cells. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. clear - SLO LO SC48. lia. }
  assert (LKCs6 : rw_cells usegs m13 LK (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))).
  { eapply rw_cells_transport; [exact LKCc6| exact MU6| exact WM6|]. unfold mutex_cells. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. clear - SLO LO LKC40. lia. }
  assert (REPos6 : plh_rep m13 LB6 L6 lh2 pl2 pb2 B2 0 (nb16 [] [] [] [] [])).
  { eapply plh_rep_munch; [exact REPoc6| exact MU6| exact WM6|]. intros a Ha. cbn [outside]. clear - Ha LO SLO. lia. }
  assert (QCos6 : rw_cells usegs m13 Q2 (sk_cells (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 PROP_SK_CMPT) (Z_to_bv 64 PROP_SK_FREET) (Z_to_bv 64 PROP_SK_COPYT))).
  { eapply rw_cells_transport; [exact QCoc6| exact MU6| exact WM6|]. unfold sk_cells. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. clear - SLO LO Q2C. lia. }
  clear FRc6 CELLc6 SCSc6 LKCc6 CSTc6 FRMo6 HPc6 STc6 MIc6 MU6 WM6 REPoc6 QCoc6 QCc6 DCc6 REPc6.
  (* [comment removed for export] *)
  clear ROB NONUL NE PAD SLOW SHIGH LEN. pose proof lit_yes as (ROB & NONUL & NE & PAD & SLOW & SHIGH & LEN).
  eapply climpl_seq.
  { eapply (pstr_first_false CM CC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m13 st6 LB6 LB L6 f6 lo Bd CTX_A S LK lh1 lh2 6 0 Q1 Q2 A_YES s_yes k_yes ps pk pq2 pl2 pb2 B2 0 (nb16 [] [] [] [] []));
      [clear - Hf FU1 FU2 FU3 FU4 FU5 FU6; lia| | exact CSTs6| rewrite unsigned_lit by (clear - SPR SP0; lia); unfold PSTR_STACK, SK_PUSH_GROW_STACK, CRE_STACK, RREALLOC_STACK, RMALLOC_STACK; clear - SLO; lia
      | reflexivity| reflexivity| reflexivity| reflexivity| unfold CTX_A; clear; lia| unfold CTX_A; clear; lia| exact CELLs6| unfold CTX_A; clear; lia
      | rewrite unsigned_lit by (clear - SPR SP0; lia); clear - SP16; lia
      | exact INS_6| exact SCSs6| clear; lia| clear; lia| clear; lia| clear; lia| exact INK_6| exact LKCs6| exact REPos6| clear; lia
      | rewrite hash_yes; cbn; repeat (constructor; [discriminate|]); constructor
      | exact INQ2_6| exact QCos6
      | exact ROB| exact NONUL| exact NE| exact PAD| exact SLOW| exact SHIGH| exact LEN
      | unfold plh_T; cbn [map concat nb16 app In]; or_cases ltac:(fun E => pneE E)| unfold plh_T; cbn [map concat nb16 app In]; or_cases ltac:(fun E => pneE E)| unfold plh_T; cbn [map concat nb16 app In]; or_cases ltac:(fun E => pneE E)
      | pne| pne| pne].
    eapply croom_weaken; [eapply croom_grow; [exact ROOM| exact GA6]| | |]; wnorm; clear; lia. }
  cbv beta. intros f7 L7r st7 msr7 (v7 & m14 & LB7r & RET7 & FU7 & GR7 & CSTc7 & FRMc7 & RES).
  destruct RES as (pn7 & An7 & pd2 & D2 & pnn7 & N7 & RES). cbv zeta in RES. rewrite hash_yes in RES.
  destruct RES as (-> & -> & -> & RA7 & RD2 & RN7 & SCSc7 & LKCc7 & REPc7 & QCc7 & DCc7 & _).
  destruct RET7 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->). cret_lit.
  wnormH GR7. pose proof (cgrow_trans _ _ _ _ _ _ _ _ _ GA6 GR7) as GA7. clear GR7.
  (* [comment removed for export] *)
  change (Z.of_nat (length s_yes) + 16) with 19 in *. change (cnt_of false 6 0 + 1) with 1 in *. cbn [ni_after vi_after t_of q_of] in SCSc7, REPc7, QCc7.
  change (0 + 1) with 1 in REPc7.
  change (lupd (Z.to_nat (H_YES mod 8)) (nth (Z.to_nat (H_YES mod 8)) (nb16 [] [] [] [] []) [] ++ [(pnn7, N7, H_YES)]) (nb16 [] [] [] [] [])) with (nb16 [] [] [] [(pnn7, N7, H_YES)] []) in REPc7.
  set (LB7 := (pnn7, N7, 24) :: (pd2, D2, 32) :: (pn7, An7, 19) :: (pnn6, N6, 24) :: (pn6, An6, 25) :: (pnn5, N5, 24) :: (q5, E5, 48) :: (pn5, An5, 21) :: (pnn4, N4, 24) :: (pn4, An4, 22) :: (pnn3, N3, 24) :: (pn3, An3, 20) :: (pnn2, N2, 24) :: (pn2, An2, 23) :: (pnn1, N1, 24) :: (pn1, An1, 24) :: LBall) in *. set (L7 := (pnn7, 24) :: (pd2, 32) :: (pn7, 19) :: L6) in *.
  pose proof CSTc7 as (HPc7 & _ & (errc7 & _ & _ & STc7 & _ & _ & MIc7 & _) & _). rewrite unsigned_lit in STc7 by (clear - SPR SP0; lia).
  pose proof FRMc7 as (CFRc7 & _). rewrite unsigned_lit in CFRc7 by (clear - SPR SP0; lia).
  destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CSTc7) as [NDL7 _]. subst LB7. cbn [map blk_id fst] in NDL7.
  pose proof (cstate_fresh_ids st7 [(pnn7, N7, 24); (pd2, D2, 32); (pn7, An7, 19); (pnn6, N6, 24); (pn6, An6, 25); (pnn5, N5, 24); (q5, E5, 48); (pn5, An5, 21); (pnn4, N4, 24); (pn4, An4, 22); (pnn3, N3, 24); (pn3, An3, 20); (pnn2, N2, 24); (pn2, An2, 23); (pnn1, N1, 24); (pn1, An1, 24)] LBall LB L _ m14 _ _ _ _ CSTc7 CO) as FRa.
  pose proof (fun q (Hq : orig LBall L q) => FRa (pnn7, N7, 24) (or_introl eq_refl) q Hq) as Fpnn7. cbn [blk_id fst] in Fpnn7.
  pose proof (fun q (Hq : orig LBall L q) => FRa (pd2, D2, 32) (or_intror (or_introl eq_refl)) q Hq) as Fpd2. cbn [blk_id fst] in Fpd2.
  clear FRa.
  pose proof (nd_neq _ 1 0 _ _ NDL7 eq_refl eq_refl ltac:(discriminate)) as Npd2pnn7.
  set (LB7 := (pnn7, N7, 24) :: (pd2, D2, 32) :: (pn7, An7, 19) :: (pnn6, N6, 24) :: (pn6, An6, 25) :: (pnn5, N5, 24) :: (q5, E5, 48) :: (pn5, An5, 21) :: (pnn4, N4, 24) :: (pn4, An4, 22) :: (pnn3, N3, 24) :: (pn3, An3, 20) :: (pnn2, N2, 24) :: (pn2, An2, 23) :: (pnn1, N1, 24) :: (pn1, An1, 24) :: LBall) in *.
  assert (INS_7 : In (ps, S, 48) LB7) by (do 16 right; exact INS). assert (INK_7 : In (pk, LK, 40) LB7) by (do 16 right; exact INK).
  assert (INQ1_7 : In (pq1, Q1, 56) LB7) by (do 16 right; exact INQ1). assert (INQ2_7 : In (pq2, Q2, 56) LB7) by (do 16 right; exact INQ2).
  assert (IND_7 : In (pd2, D2, 32) LB7) by (do 1 right; left; reflexivity).
  assert (FRMo7 : cframe (ppk_T (PPK ps pk pl1 pb1 pl2 pb2 pq1 pq2 S LK lh1 B1 lh2 B2 Q1 Q2)) [] (bv_unsigned sp) s LBall L m st7 LB7 L7 m14).
  { eapply cframe_call; [exact FRMs6| exact FRMc7| rewrite unsigned_lit by (clear - SPR SP0; lia); clear; lia| intros a X; exact X|].
    intros q Hq NT. unfold pstr_T1, plh_T. cbn [map concat nb16 app In]. or_cases ltac:(fun E => ht_leaf q Hq NT E). }
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFRc7 FRs6 ltac:(clear; lia)) as FRc7.
  assert (CELLc7 := cfr_cells_static _ _ _ _ _ _ _ _ CFRc7 CELLs6). cbn [cells_size csize Nat.add] in CELLc7. unfold CTX_A in CELLc7.
  specialize (CELLc7 ltac:(clear; lia) ltac:(clear; lia) ltac:(intros a Ha; unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP, LX_FLAGS; cbn [rin_ivs fst snd]; clear - Ha; lia)).
  clear FRs6 CELLs6 CSTs6  FRMc7 CFRc7 FRMs6.
  (* [comment removed for export] *)
  eapply climpl_evt. { eapply (ppi_seg7 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m14 lo); [exact STc7| clear - LO Sg0 SC48; lia| clear - SLO; lia| clear - SP0; lia| exact MIc7]. }
  cbv beta. intros ms8 (m15 & -> & MU7 & WM7 & MIs7 & STs7).
  assert (CSTs7 : cstate st7 LB7 LB L7 m15 (Z_to_bv 64 (bv_unsigned sp + -48)) tp lo Bd).
  { eapply (cstate_seg _ _ _ _ _ m14 m15 _ _ tp lo Bd (bv_unsigned sp + -48)); [exact CSTc7| exact MU7| exact WM7| exact MIs7| | clear - SPR SLO LO GLO; lia| clear - SPB SP0; lia| | rewrite unsigned_lit by (clear - SPR SP0; lia); exact STs7| rewrite unsigned_lit by (clear - SPR SP0; lia); clear - SPB SPR SP0; lia].
    - constructor; [apply cwin_stack; clear - SPR SLO LO GLO; lia| constructor].
    - cbn [disjoint_from]. unfold LX_FLAGS. clear - SPR GLO SLO. lia. }
  assert (FRMs7 : cframe (ppk_T (PPK ps pk pl1 pb1 pl2 pb2 pq1 pq2 S LK lh1 B1 lh2 B2 Q1 Q2)) [] (bv_unsigned sp) s LBall L m st7 LB7 L7 m15).
  { eapply cframe_seg; [exact FRMo7| exact MU7| exact WM7| exact HPc7| clear - LO SLO SPR GLO; lia|]. constructor; [apply cseg_ok_stack; clear - LO SLO SPR GLO; lia| constructor]. }
  assert (FRs7 : rw_cells usegs m15 (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { eapply rw_cells_transport; [exact FRc7| exact MU7| exact WM7|]. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. clear - SPR SP0. lia. }
  assert (CELLs7 : rw_cells usegs m15 (CTX_A + 168) [C8 (Z_to_bv 64 S)]).
  { eapply rw_cells_transport; [exact CELLc7| exact MU7| exact WM7|]. unfold CTX_A. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. clear - SLO GLO. lia. }
  assert (SCSs7 : rw_cells usegs m15 S (psd_cells LK lh1 lh2 6 1 Q1 Q2)).
  { eapply rw_cells_transport; [exact SCSc7| exact MU7| exact WM7|]. unfold psd_cells. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. clear - SLO LO SC48. lia. }
  assert (LKCs7 : rw_cells usegs m15 LK (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))).
  { eapply rw_cells_transport; [exact LKCc7| exact MU7| exact WM7|]. unfold mutex_cells. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. clear - SLO LO LKC40. lia. }
  assert (QCs7 : rw_cells usegs m15 Q2 (sk_cells (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 D2) (Z_to_bv 64 1) (Z_to_bv 64 4) (Z_to_bv 64 0) (Z_to_bv 64 PROP_SK_CMPT) (Z_to_bv 64 PROP_SK_FREET) (Z_to_bv 64 PROP_SK_COPYT))).
  { eapply rw_cells_transport; [exact QCc7| exact MU7| exact WM7|]. unfold sk_cells. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. clear - SLO LO Q2C. lia. }
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CSTc7 IND_7) as (Dg0_7 & _ & _ & DCg_7 & _).
  assert (DCs7 : rw_cells usegs m15 D2 [CB (8 + 24)%nat (le8 (Z_to_bv 64 (An7 + 12)) ++ repeat (Z_to_bv 8 0) 24)]).
  { apply cells_C8_CB; [reflexivity|]. eapply rw_cells_transport; [exact DCc7| exact MU7| exact WM7|]. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. clear - SLO LO DCg_7. lia. }
  assert (REPs7 : plh_rep m15 LB7 L7 lh2 pl2 pb2 B2 1 (nb16 [] [] [] [(pnn7, N7, H_YES)] [])).
  { eapply plh_rep_munch; [exact REPc7| exact MU7| exact WM7|]. intros a Ha. cbn [outside]. clear - Ha LO SLO. lia. }
  clear FRc7 CELLc7 SCSc7 LKCc7 CSTc7 FRMo7 HPc7 STc7 MIc7 MU7 WM7 QCc7 DCc7 REPc7.
  (* [comment removed for export] *)
  clear ROB NONUL NE PAD SLOW SHIGH LEN. pose proof lit_no as (ROB & NONUL & NE & PAD & SLOW & SHIGH & LEN).
  eapply climpl_seq.
  { eapply (pstr_room_false CM PUSHR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m15 st7 LB7 LB L7 f7 lo Bd CTX_A S LK lh1 lh2 6 1 Q1 Q2 A_NO s_no k_no ps pk pq2 pd2 pl2 pb2 B2 1 (nb16 [] [] [] [(pnn7, N7, H_YES)] []) D2 1 4 1);
      [clear - Hf FU1 FU2 FU3 FU4 FU5 FU6 FU7; lia| | exact CSTs7| rewrite unsigned_lit by (clear - SPR SP0; lia); unfold PSTR_STACK, SK_PUSH_GROW_STACK, CRE_STACK, RREALLOC_STACK, RMALLOC_STACK; clear - SLO; lia
      | reflexivity| reflexivity| reflexivity| reflexivity| unfold CTX_A; clear; lia| unfold CTX_A; clear; lia| exact CELLs7| unfold CTX_A; clear; lia
      | rewrite unsigned_lit by (clear - SPR SP0; lia); clear - SP16; lia
      | exact INS_7| exact SCSs7| clear; lia| clear; lia| clear; lia| clear; lia| exact INK_7| exact LKCs7| exact REPs7| clear; lia
      | rewrite hash_no; cbn; repeat (constructor; [discriminate|]); constructor
      | exact INQ2_7| exact QCs7| clear; lia| clear; lia| clear; lia| clear; lia| exact IND_7| exact DCs7
      | exact ROB| exact NONUL| exact NE| exact PAD| exact SLOW| exact SHIGH| exact LEN
      | unfold plh_T; cbn [map concat nb16 app In]; or_cases ltac:(fun E => pneE E)| unfold plh_T; cbn [map concat nb16 app In]; or_cases ltac:(fun E => pneE E)| unfold plh_T; cbn [map concat nb16 app In]; or_cases ltac:(fun E => pneE E)| unfold plh_T; cbn [map concat nb16 app In]; or_cases ltac:(fun E => pneE E)
      | pne| pne| pne| pne| pne| pne].
    eapply croom_weaken; [eapply croom_grow; [exact ROOM| exact GA7]| | |]; wnorm; clear; lia. }
  cbv beta. intros f8 L8r st8 msr8 (v8 & m16 & LB8r & RET8 & FU8 & GR8 & CSTc8 & FRMc8 & RES).
  destruct RES as (pn8 & An8 & pnn8 & N8 & jk8 & RES). cbv zeta in RES. rewrite hash_no in RES.
  destruct RES as (-> & -> & -> & RA8 & RN8 & SCSc8 & LKCc8 & REPc8 & QCc8 & DCc8 & _).
  destruct RET8 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->). cret_lit.
  wnormH GR8. pose proof (cgrow_trans _ _ _ _ _ _ _ _ _ GA7 GR8) as GA8. clear GR8.
  (* [comment removed for export] *)
  change (Z.of_nat (length s_no) + 16) with 18 in *. change (cnt_of false 6 1 + 1) with 2 in *. cbn [ni_after vi_after t_of q_of] in SCSc8, REPc8, QCc8.
  change (1 + 1) with 2 in REPc8.
  change (lupd (Z.to_nat (H_NO mod 8)) (nth (Z.to_nat (H_NO mod 8)) (nb16 [] [] [] [(pnn7, N7, H_YES)] []) [] ++ [(pnn8, N8, H_NO)]) (nb16 [] [] [] [(pnn7, N7, H_YES)] [])) with (nb16 [] [] [(pnn8, N8, H_NO)] [(pnn7, N7, H_YES)] []) in REPc8.
  set (LB8 := (pnn8, N8, 24) :: (pn8, An8, 18) :: (pnn7, N7, 24) :: (pd2, D2, 32) :: (pn7, An7, 19) :: (pnn6, N6, 24) :: (pn6, An6, 25) :: (pnn5, N5, 24) :: (q5, E5, 48) :: (pn5, An5, 21) :: (pnn4, N4, 24) :: (pn4, An4, 22) :: (pnn3, N3, 24) :: (pn3, An3, 20) :: (pnn2, N2, 24) :: (pn2, An2, 23) :: (pnn1, N1, 24) :: (pn1, An1, 24) :: LBall) in *. set (L8 := (pnn8, 24) :: (pn8, 18) :: L7) in *.
  pose proof CSTc8 as (HPc8 & _ & (errc8 & _ & _ & STc8 & _ & _ & MIc8 & _) & _). rewrite unsigned_lit in STc8 by (clear - SPR SP0; lia).
  pose proof FRMc8 as (CFRc8 & _). rewrite unsigned_lit in CFRc8 by (clear - SPR SP0; lia).
  destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CSTc8) as [NDL8 _]. subst LB8. cbn [map blk_id fst] in NDL8.
  pose proof (cstate_fresh_ids st8 [(pnn8, N8, 24); (pn8, An8, 18); (pnn7, N7, 24); (pd2, D2, 32); (pn7, An7, 19); (pnn6, N6, 24); (pn6, An6, 25); (pnn5, N5, 24); (q5, E5, 48); (pn5, An5, 21); (pnn4, N4, 24); (pn4, An4, 22); (pnn3, N3, 24); (pn3, An3, 20); (pnn2, N2, 24); (pn2, An2, 23); (pnn1, N1, 24); (pn1, An1, 24)] LBall LB L _ m16 _ _ _ _ CSTc8 CO) as FRa.
  pose proof (fun q (Hq : orig LBall L q) => FRa (pnn8, N8, 24) (or_introl eq_refl) q Hq) as Fpnn8. cbn [blk_id fst] in Fpnn8.
  clear FRa.
  set (LB8 := (pnn8, N8, 24) :: (pn8, An8, 18) :: (pnn7, N7, 24) :: (pd2, D2, 32) :: (pn7, An7, 19) :: (pnn6, N6, 24) :: (pn6, An6, 25) :: (pnn5, N5, 24) :: (q5, E5, 48) :: (pn5, An5, 21) :: (pnn4, N4, 24) :: (pn4, An4, 22) :: (pnn3, N3, 24) :: (pn3, An3, 20) :: (pnn2, N2, 24) :: (pn2, An2, 23) :: (pnn1, N1, 24) :: (pn1, An1, 24) :: LBall) in *.
  assert (INS_8 : In (ps, S, 48) LB8) by (do 18 right; exact INS). assert (INK_8 : In (pk, LK, 40) LB8) by (do 18 right; exact INK).
  assert (INQ1_8 : In (pq1, Q1, 56) LB8) by (do 18 right; exact INQ1). assert (INQ2_8 : In (pq2, Q2, 56) LB8) by (do 18 right; exact INQ2).
  assert (IND_8 : In (pd2, D2, 32) LB8) by (do 3 right; left; reflexivity).
  assert (FRMo8 : cframe (ppk_T (PPK ps pk pl1 pb1 pl2 pb2 pq1 pq2 S LK lh1 B1 lh2 B2 Q1 Q2)) [] (bv_unsigned sp) s LBall L m st8 LB8 L8 m16).
  { eapply cframe_call; [exact FRMs7| exact FRMc8| rewrite unsigned_lit by (clear - SPR SP0; lia); clear; lia| intros a X; exact X|].
    intros q Hq NT. unfold pstr_T, plh_T. cbn [map concat nb16 app In]. or_cases ltac:(fun E => ht_leaf q Hq NT E). }
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFRc8 FRs7 ltac:(clear; lia)) as FRc8.
  assert (CELLc8 := cfr_cells_static _ _ _ _ _ _ _ _ CFRc8 CELLs7). cbn [cells_size csize Nat.add] in CELLc8. unfold CTX_A in CELLc8.
  specialize (CELLc8 ltac:(clear; lia) ltac:(clear; lia) ltac:(intros a Ha; unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP, LX_FLAGS; cbn [rin_ivs fst snd]; clear - Ha; lia)).
  clear FRs7 CELLs7 CSTs7  FRMc8 CFRc8 FRMs7.
  (* [comment removed for export] *)
  eapply climpl_evt. { eapply (ppi_seg8 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m16 lo ra s0 s1 s2 s3 s4); [exact STc8| clear - LO Sg0 SC48; lia| clear - SLO; lia| clear - SP0; lia| exact MIc8| exact FRc8]. }
  cbv beta. intros ms9 (a1f & m17 & -> & MU8 & WM8 & MIs8 & STs8).
  assert (CSTs8 : cstate st8 LB8 LB L8 m17 sp tp lo Bd).
  { eapply (cstate_seg _ _ _ _ _ m16 m17 _ _ tp lo Bd (bv_unsigned sp)); [exact CSTc8| exact MU8| exact WM8| exact MIs8| | clear - SPR SLO LO GLO; lia| exact SPB| | exact STs8| exact SPB].
    - constructor; [apply cwin_stack; clear - SPR SLO LO GLO; lia| constructor].
    - cbn [disjoint_from]. unfold LX_FLAGS. clear - SPR GLO SLO. lia. }
  assert (FRMs8 : cframe (ppk_T (PPK ps pk pl1 pb1 pl2 pb2 pq1 pq2 S LK lh1 B1 lh2 B2 Q1 Q2)) [] (bv_unsigned sp) s LBall L m st8 LB8 L8 m17).
  { eapply cframe_seg; [exact FRMo8| exact MU8| exact WM8| exact HPc8| clear - LO SLO SPR GLO; lia|]. constructor; [apply cseg_ok_stack; clear - LO SLO SPR GLO; lia| constructor]. }
  (* [comment removed for export] *)
  apply climpl_done. exists (Z_to_bv 64 1), m17, LB8.
  split; [unfold cret; do 14 eexists; reflexivity|].
  split; [clear - Hf FU1 FU2 FU3 FU4 FU5 FU6 FU7 FU8; lia|].
  split; [eapply cgrow_weaken; [exact GA8| clear; lia| clear; lia| clear; lia]|].
  split; [exact CSTs8|]. split; [exact FRMs8|].
  unfold ppi_res. exists pn1, pnn1, pn2, pnn2, pn3, pnn3, pn4, pnn4, pn5, q5, pnn5, pn6, pnn6, pn7, pd2, pnn7, pn8, pnn8.
  exists An1, N1, An2, N2, An3, N3, An4, N4, An5, E5, N5, An6, N6, An7, D2, N7, An8, N8.
  split; [reflexivity|]. split; [subst LB8; reflexivity|].
  repeat match goal with |- _ /\ _ => split end; assumption.
Qed.

End WithCeiling0.
