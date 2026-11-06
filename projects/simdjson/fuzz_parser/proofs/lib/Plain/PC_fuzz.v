(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import Stdio_pure Printf_pieces.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import PImg.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import RMallocRep RMallocTree RMalloc_iface ROpNew_iface ROpNew ROpNew_nt.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require RMalloc_ifaceP.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim Monad Stdio Malloc HarnessP ProgP SjStage1 SjS1Bytes.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import RunDraw.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import PC_kit PC_docdtor PC_impldtor PC_dtor PC_s12iface PC_pid PU_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation mem := (word -> option byte).

Section CANSEC1. Context {rc : runConstT}.
Section Proof.
  Hypothesis ONT : opnew_nt_stmt.
  Hypothesis ODA : opdelete_arr_stmt.
  Hypothesis OD : opdelete_stmt.
  Hypothesis PARSE : parse_stmt.

  Theorem fuzz_proof : fuzz_oneU_stmt ProgP.fuzz_one.
  Proof.
    unfold fuzz_oneU_stmt. intros until errv. intros HP DAT DB DCR DWR D0 DTOP DL CS AUX SPB SP47 ST LOA LOS ERR MI FZ TP SPA A0 A1 RA.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    unfold PHARNESS_STACK in LOS. atop_facts.
    subst tp. rewrite errno_lit in ERR. unfold RERRNO in ERR.
    destruct CS as (CI & FA & CST).
    set (len := zlength payload) in *.
    pose proof (RMalloc_ifaceP.RHEAP_block_range_proof s LB m) as LBR.
    assert (LBB : forall b, In b LB -> blk_addr b + blk_size b <= ATOP) by (intros b Hb; destruct (LBR b HP Hb) as (_ & _ & _ & R4 & _); exact R4).
    clear LBR.
    remember (map (Z_to_bv 8) payload) as bs eqn:EBS.
    assert (BSL : Z.of_nat (length bs) = len) by (subst bs; unfold len, zlength; rewrite length_map; reflexivity).
    (* [comment removed for export] *)
    assert (DSEP : D + len <= lo \/ bv_unsigned sp <= D).
    { destruct DCR as [H|[H|(b & Hb & H1 & H2)]]; [right; lia| left; lia| left; pose proof (LBB b Hb); lia]. }
    destruct CI as (CI1 & CI2 & CI3 & CI4). unfold PVTAB_IMPL, vtab_impl_cells in CI1. unfold PVTAB_DOM, vtab_dom_cells in CI2.
    unfold PGOT_NOTHROW, got_nothrow_cells, PNOTHROW in CI3. unfold PFMIN, fmin_cells in CI4.
    unfold ProgP.fuzz_one, HarnessP.fuzz_one.
    apply implM_from_evt.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl psegs m) as WM.
    carve_frame 112%nat ST.
    pose proof (stk_of_cells _ _ _ FR) as FSTK. cbn [cells_size csize] in FSTK. change (Z.of_nat 112) with 112 in FSTK.
    replace (bv_unsigned sp + -112 + 112) with (bv_unsigned sp) in FSTK by lia.
    subst a0 a1. unfold PFUZZ_ENTRY.
    do 23 zstep.
    apply evt_done.
    (* [comment removed for export] *)
    lazymatch goal with H : rw_cells psegs ?mm (bv_unsigned sp + -112) ?cs |- _ =>
      destruct (rw_cells_cut psegs mm _ cs 1 H) as [FRR F1]; clear H end.
    cbn [firstn skipn cells_size csize Nat.add] in FRR, F1. change (Z.of_nat 24) with 24 in F1.
    destruct (rw_cells_cut psegs _ _ _ 2 F1) as [_ F2]; clear F1. cbn [firstn skipn cells_size csize Nat.add] in F2. change (Z.of_nat 8) with 8 in F2.
    destruct (rw_cells_cut psegs _ _ _ 1 F2) as [PIM F3]; clear F2. cbn [firstn skipn cells_size csize Nat.add] in PIM, F3. change (Z.of_nat 8) with 8 in F3.
    destruct (rw_cells_cut psegs _ _ _ 3 F3) as [_ F4]; clear F3. cbn [firstn skipn cells_size csize Nat.add] in F4. change (Z.of_nat 8) with 8 in F4.
    destruct (rw_cells_cut psegs _ _ _ 3 F4) as [PDOC F5]; clear F4. cbn [firstn skipn cells_size csize Nat.add] in PDOC, F5. change (Z.of_nat 24) with 24 in F5.
    destruct (rw_cells_cut psegs _ _ _ 2 F5) as [PMAX F6]; clear F5. cbn [firstn skipn cells_size csize Nat.add] in PMAX, F6. change (Z.of_nat 9) with 9 in F6.
    destruct (rw_cells_cut psegs _ _ _ 1 F6) as [_ F7]; clear F6. cbn [firstn skipn cells_size csize Nat.add] in F7. change (Z.of_nat 7) with 7 in F7.
    destruct (rw_cells_cut psegs _ _ _ 2 F7) as [PCP FRA]; clear F7. cbn [firstn skipn cells_size csize Nat.add] in PCP, FRA. change (Z.of_nat 16) with 16 in FRA.
    replace (bv_unsigned sp + -112 + 24 + 8) with (bv_unsigned sp + -88 + 8) in PIM by lia.
    replace (bv_unsigned sp + -112 + 24 + 8 + 8 + 8) with (bv_unsigned sp + -88 + 24) in PDOC by lia.
    replace (bv_unsigned sp + -112 + 24 + 8 + 8 + 8 + 24) with (bv_unsigned sp + -88 + 48) in PMAX by lia.
    replace (bv_unsigned sp + -112 + 24 + 8 + 8 + 8 + 24 + 9 + 7) with (bv_unsigned sp + -88 + 64) in PCP by lia.
    replace (bv_unsigned sp + -112 + 24 + 8 + 8 + 8 + 24 + 9 + 7 + 16) with (bv_unsigned sp + -8) in FRA by lia.
    destruct (stk_split psegs _ _ (bv_unsigned sp + -8) _ FSTK ltac:(lia)) as [RSTK _]. clear FSTK.
    replace (bv_unsigned sp + -8) with (bv_unsigned sp + -88 + 80) in RSTK by lia.
    pose proof (cstat_transport _ _ (stat_pres_of_munch _ _ _ MU WM ltac:(intros a Ha; cbn; lia)) CST) as CST1. clear CST.
    lazymatch goal with |- implM _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (HP1 : RHEAP s LB mx) by (eapply RHEAP_stack_frame; [exact HP| exact MU| exact WM| repeat constructor; cbn; lia]);
      assert (AUX1 : rauxv_ok mx AB) by (eapply rauxv_ok_stack_frame; [exact AUX| exact MU| exact WM| repeat constructor; cbn; lia])
    end.
    (* [comment removed for export] *)
    eapply implM_bind.
    { eapply (pid_proof ONT PARSE) with (lo := lo) (B := AB) (D := D) (P := bv_unsigned sp + -88) (R := bv_unsigned sp + -112);
        rewrite ?unsigned_lit by lia;
        [ exact HP1 | subst bs; exact DAT | exact DB | eapply rclient_range_sp; [exact DCR| lia] | exact D0 | exact DTOP | exact DL | exact DWR
        | split; [exact CI1|]; split; [exact CI2|]; split; [exact CI3| exact CI4]
        | exact CST1 | exact AUX1 | lia | lia | lia | exact ST | exact LOA
        | unfold PID_STACK, PARSE_STACK, PS2_STACK, OPNEW_NT_STACK, OPNEW_STACK, RMALLOC_STACK; lia
        | rewrite errno_lit; exact ERR | exact MI | exact FZ | reflexivity
        | exact PIM | exact PDOC | exact PMAX | exact PCP | exact FRR | lia | lia | lia | lia | exact RSTK
        | reflexivity | reflexivity | unfold w64; f_equal; lia | reflexivity | reflexivity | reflexivity ]. }
    cbv beta. intros [[[psb ptp] [[[pim psi] poc] pia]] lb] s1' ms1 PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F1 & fc1 & m2 & errv2 & -> & FZ2 & MI2 & ST2 & ERR2 & AUX2
                    & PW2 & FAE2 & SOE2 & CSB2 & RSTK2 & RR2).
    destruct RR2 as (ASB & ATP & AIM & ASI & AOC & AIA & ACP & HP2 & PIM2 & PDOC2 & PCP2 & IM0 & IM16 & IM56).
    rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in PW2 by lia. rewrite errno_lit in ERR2. unfold RERRNO in ERR2.
    lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?r)] => replace (ret_pc (Z_to_bv 64 r)) with (Z_to_bv 64 r) by (symmetry; rpc) end.
    (* [comment removed for export] *)
    assert (TW : forall A cs, rw_cells psegs m1 A cs -> rclient_range LB (bv_unsigned sp + -112) A (Z.of_nat (cells_size cs)) ->
               disjoint_from ([(bv_unsigned sp + -88, bv_unsigned sp + -88 + 80); (bv_unsigned sp + -112, bv_unsigned sp + -112 + 24)] ++ client_wr)
                 A (Z.of_nat (cells_size cs)) -> rw_cells psegs m2 A cs).
    { intros A cs H HR HD. exact (rheap_pres_W_rw_cells _ _ _ _ _ _ _ PW2 H HR HD). }
    assert (FRA2 : rw_cells psegs m2 (bv_unsigned sp + -8) [C8 ra]) by (apply TW; [exact FRA| left; cbn; lia| cbn; lia]).
    assert (CI12 : rw_cells psegs m2 469608 (vtab_impl_cells)) by (apply TW; [exact CI1| right; left; unfold RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP; cbn; lia| cbn; lia]).
    assert (CI22 : rw_cells psegs m2 469712 (vtab_dom_cells)) by (apply TW; [exact CI2| right; left; unfold RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP; cbn; lia| cbn; lia]).
    assert (CI32 : rw_cells psegs m2 482752 [C8 (Z_to_bv 64 113616)]) by (apply TW; [exact CI3| right; left; unfold RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP; cbn; lia| cbn; lia]).
    assert (CI42 : rw_cells psegs m2 487120 [C4 (Z_to_bv 64 8388608)]) by (apply TW; [exact CI4| right; left; unfold RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP; cbn; lia| cbn; lia]).
    clear TW FRA CI1 CI2 CI3 CI4.
    destruct (stk_split psegs _ _ (bv_unsigned sp + -88) _ RSTK2 ltac:(lia)) as [RSTKR PSTK2]. clear RSTK2.
    (* [comment removed for export] *)
    apply implM_from_evt.
    do 2 zstep.
    apply evt_done.
    eapply implM_bind.
    { eapply (pdtor_proof ODA OD) with (lo := lo) (B := AB) (P := bv_unsigned sp + -88) (LB0 := LB) (lb := lb) (ACP := ACP) (ncp := COPY_BYTES len);
        rewrite ?unsigned_lit by lia;
        [ unfold pid_blocks in HP2; rewrite <- app_assoc in HP2; exact HP2 | unfold IMPL_BYTES; lia | exact AUX2 | lia | exact ST2 | exact LOA
        | unfold PDTOR_STACK, RFREE_STACK; lia | rewrite errno_lit; exact ERR2 | exact MI2 | reflexivity | exact CI22
        | exact PIM2 | exact PDOC2 | exact PCP2 | lia | lia | exact PSTK2 | exact IM0 | exact IM16 | exact IM56 | f_equal; lia ]. }
    cbv beta. intros [] s2' ms2 PO.
    destruct PO as (v0 & v1 & v2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m3 & errv3 & -> & MI3 & ST3 & ERR3 & AUX3 & PX3 & FAE3
                    & SOE3 & HP3 & PSTK3).
    rewrite ?unsigned_lit in ST3 by lia. rewrite ?unsigned_lit in PX3 by lia. rewrite errno_lit in ERR3. unfold RERRNO in ERR3.
    lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?r)] => replace (ret_pc (Z_to_bv 64 r)) with (Z_to_bv 64 r) by (symmetry; rpc) end.
    assert (TX : forall A cs, rw_cells psegs m2 A cs -> rclient_range LB (bv_unsigned sp + -112) A (Z.of_nat (cells_size cs)) ->
               (A + Z.of_nat (cells_size cs) <= bv_unsigned sp + -88 + 8 \/ bv_unsigned sp + -88 + 8 + 64 <= A) -> rw_cells psegs m3 A cs).
    { intros A cs H HR HD. exact (rheap_pres_x_rw_cells _ _ _ _ _ _ _ _ PX3 H HR HD). }
    assert (FRA3 : rw_cells psegs m3 (bv_unsigned sp + -8) [C8 ra]) by (apply TX; [exact FRA2| left; cbn; lia| cbn; lia]).
    assert (CI13 : rw_cells psegs m3 469608 (vtab_impl_cells)) by (apply TX; [exact CI12| right; left; unfold RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP; cbn; lia| cbn; lia]).
    assert (CI23 : rw_cells psegs m3 469712 (vtab_dom_cells)) by (apply TX; [exact CI22| right; left; unfold RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP; cbn; lia| cbn; lia]).
    assert (CI33 : rw_cells psegs m3 482752 [C8 (Z_to_bv 64 113616)]) by (apply TX; [exact CI32| right; left; unfold RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP; cbn; lia| cbn; lia]).
    assert (CI43 : rw_cells psegs m3 487120 [C4 (Z_to_bv 64 8388608)]) by (apply TX; [exact CI42| right; left; unfold RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP; cbn; lia| cbn; lia]).
    pose proof (cstat_transport _ _ (stat_pres_of_x _ _ _ _ _ _ PX3 ltac:(lia)) (or_intror CSB2)) as CS3.
    assert (RSTKR3 : stk psegs m3 (bv_unsigned sp + -112) (bv_unsigned sp + -88)) by (eapply rheap_pres_x_stk; [exact PX3| exact RSTKR| lia| lia]).
    clear TX FRA2 CI12 CI22 CI32 CI42 RSTKR.
    (* [comment removed for export] *)
    apply implM_ret.
    pose proof (stk_of_cells _ _ _ FRA3) as FASTK. cbn [cells_size csize] in FASTK. change (Z.of_nat 8) with 8 in FASTK.
    do 4 zstep.
    assert (STF : stk psegs m3 lo (bv_unsigned sp)).
    { eapply stk_merge; [exact ST3| | lia]. eapply stk_merge; [exact RSTKR3| | lia]. eapply stk_merge; [exact PSTK3| | lia].
      replace (bv_unsigned sp + -88 + 80) with (bv_unsigned sp + -8) by lia. replace (bv_unsigned sp) with (bv_unsigned sp + -8 + 8) at 2 by lia. exact FASTK. }
    apply evt_done.
    unfold fuzz_oneU_post. do 14 eexists. exists F1, fc1, m3, errv3, LB. split; [subst ra; reflexivity|].
    split; [reflexivity|]. split; [exact MI3|]. split; [exact FZ2|]. split; [exact STF|]. split; [rewrite errno_lit; exact ERR3|].
    split; [exact AUX3|].
    split.
    { intros a Ha Hc Hw.
      assert (Hc' : rclient_addr LB (bv_unsigned sp + -112) a) by (destruct Hc as [Hc|[Hc|Hc]]; [left; lia| right; left; exact Hc| right; right; exact Hc]).
      assert (OUTL : bv_unsigned sp <= a \/ a < lo) by (destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [left; lia| right; unfold ralloc_static in Hc; lia| right; pose proof (LBB b Hb); lia]).
      assert (E1 : m1 (wa a) = m (wa a)) by (apply MU; unfold wa; rewrite unsigned_lit by lia; cbn; split; [lia| exact I]).
      destruct (PW2 a Ha Hc' ltac:(apply outside_app; split; [cbn; repeat split; try exact I; lia| exact Hw])) as [E2 W2].
      destruct (PX3 a Ha Hc' ltac:(lia)) as [E3 W3].
      split; [congruence| intros Hv; apply W3, W2, WM, Hv]. }
    split; [exact HP3|].
    split; [split; [split; [exact CI13|]; split; [exact CI23|]; split; [exact CI33| exact CI43]| split; [congruence| exact CS3]]|].
    split; [congruence|]. split; [reflexivity| congruence].
  Qed.
End Proof.
End CANSEC1.
