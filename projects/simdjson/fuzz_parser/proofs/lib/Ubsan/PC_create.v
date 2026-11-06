(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import Stdio_pure Printf_pieces.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Ubsan Require Import UImg.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Ubsan Require Import RMallocRep RMallocTree RMalloc_iface ROpNew_iface ROpNew ROpNew_nt.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Ubsan Require RMalloc_ifaceP.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim Monad Stdio Malloc HarnessP ProgP.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Ubsan Require Import RunDraw.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Ubsan Require Import PC_kit PC_ukit PC_setcap PC_setdepth PU_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation mem := (word -> option byte).


Section CANSEC1. Context {rc : runConstT}.
Definition PCREATE : Z := 0x27ca8.
Definition CREATE_STACK : Z := 64 + OPNEW_NT_STACK.
Definition w64 (z : Z) : word := Z_to_bv 64 z.

(* [comment removed for export] *)
Definition impl_cells (p1 p2 pad : list byte) (ASI cap AOC AIA : Z) : list cell :=
  [C8 (w64 PVTAB_DOM); C4 (w64 0); CB 4 p1; C8 (w64 ASI); C4 (w64 0); CB 4 p2; C8 (w64 cap); C8 (w64 MAX_DEPTH);
   C2 (w64 0); CB 6 pad; C8 (w64 AOC); C8 (w64 AIA); C8 (w64 0); C8 (w64 0); C8 (w64 0)].

Definition create_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB : list block) (len lo B DST : Z) (m : mem) (r : bptr * bptr * bptr * bptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' (errno_addr tp) [C4 errv'] /\ rauxv_ok m' B
    /\ rheap_pres_x LB (bv_unsigned sp) DST 8 m m'
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ let '(im, si, oc, ia) := r in
       exists AIM ASI AOC AIA p1 p2 pad jsi joc jia,
         rblock_range AIM IMPL_BYTES /\ rblock_range ASI (SIDX_BYTES len) /\ rblock_range AOC OC_BYTES /\ rblock_range AIA ISARR_BYTES
         /\ RHEAP s' ((ia, AIA, ISARR_BYTES) :: (oc, AOC, OC_BYTES) :: (si, ASI, SIDX_BYTES len) :: (im, AIM, IMPL_BYTES) :: LB) m'
         /\ rw_cells usegs m' DST [C8 (w64 AIM)]
         /\ rw_cells usegs m' AIM (impl_cells p1 p2 pad ASI (CAP len) AOC AIA)
         /\ rw_cells usegs m' ASI [C4 (w64 0); CB (Z.to_nat (SIDX_BYTES len - 4)) jsi]
         /\ rw_cells usegs m' AOC [CB (Z.to_nat OC_BYTES) joc] /\ rw_cells usegs m' AIA [CB (Z.to_nat ISARR_BYTES) jia].

Definition create_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (len lo B DST : Z) (errv : word),
  RHEAP s LB m ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk usegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - CREATE_STACK ->
  rw_cells usegs m (errno_addr tp) [C4 errv] ->
  mem_inv usegs m ->
  tp = Z_to_bv 64 RATP ->
  rw_cells usegs m PGOT_NOTHROW [C8 (Z_to_bv 64 PNOTHROW)] ->
  rw_cells usegs m PVTAB_DOM vtab_dom_cells ->
  rw_cells usegs m DST [C8 (w64 0)] -> bv_unsigned sp <= DST -> DST + 8 <= B ->
  0 <= len < 2^26 ->
  a1 = Z_to_bv 64 (CAP len) -> a2 = Z_to_bv 64 MAX_DEPTH -> a3 = Z_to_bv 64 DST ->
  implM usegs (HarnessP.impl_create raw_malloc ProgP.new_handler len) s
        (create_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB len lo B DST m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 PCREATE) fc None m (seg_rom usegs)).

Section Proof.
  Hypothesis ONT : opnew_nt_stmt.
  Theorem create_proof : create_stmt.
  Proof.
    unfold create_stmt. intros until errv. intros HP AUX SPB ST LOA LOS ERR MI TP GOT VT DC DSP DTOP HL A1 A2 A3.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    unfold CREATE_STACK, OPNEW_NT_STACK, OPNEW_STACK, RMALLOC_STACK in LOS. atop_facts.
    subst tp. rewrite errno_lit in ERR. unfold RERRNO in ERR. unfold PGOT_NOTHROW, PNOTHROW in GOT.
    unfold PVTAB_DOM, vtab_dom_cells in VT.
    pose proof (RMalloc_ifaceP.RHEAP_block_range_proof s LB m) as LBR.
    assert (LBB : forall b, In b LB -> blk_addr b + blk_size b <= ATOP) by (intros b Hb; destruct (LBR b HP Hb) as (_ & _ & _ & R4 & _); exact R4).
    clear LBR.
    unfold HarnessP.impl_create.
    apply implM_from_evt.
    pose proof (munch_refl [(lo, bv_unsigned sp); (DST, DST + 8)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    carve_frame 32%nat ST.
    subst a1 a2 a3. unfold PCREATE, w64 in *.
    assert (CAPR : 32 <= CAP len < 2^26 + 32) by (unfold CAP; lia).
    assert (SIDXGE : 36 <= SIDX_BYTES len)
      by (unfold SIDX_BYTES; pose proof (ROUNDUP64_bounds (CAP len) ltac:(lia)); lia).
    do 12 zstep.
    apply evt_done.
    lazymatch goal with |- implM _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (HP1 : RHEAP s LB mx) by (eapply RHEAP_stack_frame; [exact HP| exact MU| exact WM| repeat constructor; cbn; lia]);
      assert (AUX1 : rauxv_ok mx B) by (eapply rauxv_ok_stack_frame; [exact AUX| exact MU| exact WM| repeat constructor; cbn; lia])
    end.
    clear HP AUX.
    eapply implM_bind.
    { eapply (proj1 ONT) with (lo := lo) (B := B) (n := IMPL_BYTES); try reflexivity; unfold RATP, IMPL_BYTES; rewrite ?unsigned_lit by lia;
        first [exact HP1 | exact AUX1 | exact ST | exact MI | (rewrite errno_lit; unfold RERRNO; exact ERR) | (unfold OPNEW_NT_STACK, OPNEW_STACK, RMALLOC_STACK; lia)
              | lia]. }
    cbv beta. intros imp s1' ms1 PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv1 & -> & MI2 & ST2 & ERR2 & AUX2 & HPR & FAE & SOE & RR).
    destruct RR as (AIM & jim & -> & BRM & HP2 & BLKM & _).
    rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in HPR by lia. rewrite errno_lit in ERR2. unfold RERRNO in ERR2.
    lazymatch goal with |- implM _ _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?r)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 r)) with (Z_to_bv 64 r) by (symmetry; rpc) end.
    lazymatch goal with FR : rw_cells usegs _ (bv_unsigned sp + -32) ?cs |- _ =>
      assert (FR2 : rw_cells usegs m2 (bv_unsigned sp + -32) cs) by (eapply rheap_pres_rw_cells; [exact HPR| exact FR| left; cbn; lia]); clear FR end.
    assert (DC2 : rw_cells usegs m2 DST [C8 (Z_to_bv 64 0)]) by (eapply rheap_pres_rw_cells; [exact HPR| exact DC| left; cbn; lia]).
    assert (GOT2 : rw_cells usegs m2 523040 [C8 (Z_to_bv 64 112848)])
      by (eapply rheap_pres_rw_cells; [exact HPR| exact GOT| right; left; unfold RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP; cbn; lia]).
    lazymatch type of VT with rw_cells _ _ _ ?cs =>
      assert (VT2 : rw_cells usegs m2 0x7c830 cs) by (eapply rheap_pres_rw_cells; [exact HPR| exact VT| right; left; unfold RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP; cbn; lia]) end.
    clear DC GOT VT ST MI ERR AUX1.
    pose proof BRM as (BRM1 & BRM2 & BRM3 & BRM4 & BRM5). unfold IMPL_BYTES in *.
    (* [comment removed for export] *)
    assert (BLKM' : rw_cells usegs m2 AIM (mk_CB_cells [8;4;4;8;4;4;8;8;2;6;8;8;8;8;8]%nat jim))
      by (pose proof (rw_cells_split_CB usegs m2 AIM [] 96%nat jim [] [8;4;4;8;4;4;8;8;2;6;8;8;8;8;8]%nat) as SPL;
          rewrite app_nil_r in SPL; cbn [app] in SPL; apply SPL; [exact BLKM| reflexivity]).
    cbn [mk_CB_cells] in BLKM'. clear BLKM.
    apply implM_from_evt.
    pose proof (munch_refl [(lo, bv_unsigned sp); (DST, DST + 8); (AIM, AIM + 96)] m2) as MU2. pose proof (wmono_refl usegs m2) as WM2.
    do 1 zstep.
    if_cases K1; zify_cond K1; [exfalso; lia|].
    (* [comment removed for export] *)
    do 2 zstep.
    if_cases KA; zify_cond KA; [exfalso; exact (KA (land15_of_mod16 AIM BRM2))|].
    do 17 zstep.
    if_cases K2; zify_cond K2; [exfalso; lia|].
    do 1 zstep.
    (* [comment removed for export] *)
    do 2 zstep.
    if_cases KB; zify_cond KB; [exfalso; exact (KB (land7_of_mod16 AIM BRM2))|].
    do 4 zstep.
    apply evt_done.
    (* [comment removed for export] *)
    lazymatch goal with OB : rw_cells usegs _ AIM ?cs |- _ =>
      destruct (rw_cells_cut usegs _ AIM cs 1 OB) as [OB0 OBR]; cbn [firstn skipn cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in OB0, OBR;
      destruct (rw_cells_cut usegs _ (AIM + 8) _ 6 OBR) as [OB1 OB2]; cbn [firstn skipn cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in OB1, OB2;
      clear OB OBR end.
    replace (AIM + 8 + Z.of_nat 32) with (AIM + 40) in OB2 by lia.
    lazymatch goal with |- implM _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (HP3 : RHEAP s1' ((imp, AIM, 96) :: LB) mx)
        by (eapply RMalloc_ifaceP.RHEAP_frame_proof; [exact HP2| exact MU2| exact WM2|];
            apply Forall_cons; [left; cbn; lia|]; apply Forall_cons; [left; cbn; lia|];
            apply Forall_cons; [right; right; exists (imp, AIM, 96); split; [left; reflexivity| cbn; lia]| apply Forall_nil]);
      assert (AUX3 : rauxv_ok mx B)
        by (eapply rauxv_ok_frame; [exact AUX2| exact MU2| exact WM2| repeat (apply Forall_cons; [cbn; unfold RAUXV_CELL in *; lia|]); apply Forall_nil])
    end.
    clear HP2 AUX2.
    eapply implM_bind.
    { eapply (setcap_proof ONT) with (lo := lo) (B := B) (IMPL := AIM) (pim := imp); try reflexivity; unfold RATP; rewrite ?unsigned_lit by lia;
        first [exact HP3 | exact AUX3 | exact ST2 | exact MI2 | (rewrite errno_lit; unfold RERRNO; exact ERR2) | exact OB1 | exact GOT2
              | (left; reflexivity) | (unfold SETCAP_STACK, OPNEW_NT_STACK, OPNEW_STACK, RMALLOC_STACK; lia) | lia]. }
    cbv beta. intros sip s2' ms2 PO.
    destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m4 & errv2 & -> & MI4 & ST4 & ERR4 & AUX4 & HPX & FAE2 & SOE2 & RR2).
    destruct RR2 as (ASI & jsi & BRS & HP4 & BLKS & OB1').
    rewrite ?unsigned_lit in ST4 by lia. rewrite ?unsigned_lit in HPX by lia. rewrite errno_lit in ERR4. unfold RERRNO in ERR4.
    lazymatch goal with |- implM _ _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?r)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 r)) with (Z_to_bv 64 r) by (symmetry; rpc) end.
    pose proof BRS as (BRS1 & BRS2 & BRS3 & BRS4 & BRS5).
    assert (INM : forall b, In b ((imp, AIM, 96) :: LB) -> blk_addr b + blk_size b <= ATOP)
      by (intros b [<-|Hb]; [cbn; lia| exact (LBB b Hb)]).
    lazymatch goal with FR : rw_cells usegs _ (bv_unsigned sp + -32) ?cs |- _ =>
      assert (FR4 : rw_cells usegs m4 (bv_unsigned sp + -32) cs)
        by (eapply rheap_pres_x_rw_cells; [exact HPX| exact FR| left; cbn; lia| cbn; lia]); clear FR end.
    assert (DC4 : rw_cells usegs m4 DST [C8 (Z_to_bv 64 AIM)])
      by (eapply rheap_pres_x_rw_cells; [exact HPX| exact DC2| left; cbn; lia| cbn; lia]).
    assert (OB0' : rw_cells usegs m4 AIM [C8 (Z_to_bv 64 510000)])
      by (eapply rheap_pres_x_rw_cells; [exact HPX| exact OB0| right; right; exists (imp, AIM, 96); split; [left; reflexivity| cbn; lia]| cbn; lia]).
    lazymatch type of OB2 with rw_cells _ _ _ ?cs =>
      assert (OB2' : rw_cells usegs m4 (AIM + 40) cs)
        by (eapply rheap_pres_x_rw_cells; [exact HPX| exact OB2| right; right; exists (imp, AIM, 96); split; [left; reflexivity| cbn; lia]| cbn; lia]) end.
    assert (GOT4 : rw_cells usegs m4 523040 [C8 (Z_to_bv 64 112848)])
      by (eapply rheap_pres_x_rw_cells; [exact HPX| exact GOT2| right; left; unfold RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP; cbn; lia| cbn; lia]).
    lazymatch type of VT2 with rw_cells _ _ _ ?cs =>
      assert (VT4 : rw_cells usegs m4 0x7c830 cs)
        by (eapply rheap_pres_x_rw_cells; [exact HPX| exact VT2| right; left; unfold RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP; cbn; lia| cbn; lia]) end.
    clear DC2 OB0 OB2 GOT2 VT2 ST2 MI2 ERR2 AUX3 OB1.
    pose proof (new_block_disj _ _ _ _ _ _ _ HP4 (or_introl eq_refl)) as NBD. cbn [blk_addr blk_size fst snd] in NBD.
    apply implM_from_evt.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m4) as MU4. pose proof (wmono_refl usegs m4) as WM4.
    (* [comment removed for export] *)
    do 2 zstep.
    if_cases KC; zify_cond KC; [exfalso; lia|].
    do 1 zstep.
    if_cases K4; zify_cond K4; [exfalso; lia|].
    do 2 zstep.
    if_cases KN; zify_cond KN; [exfalso; lia|].
    do 2 zstep.
    if_cases KD; zify_cond KD; [exfalso; exact (KD (land7_of_mod16 AIM BRM2))|].
    do 4 zstep.
    apply evt_done.
    lazymatch type of OB2' with rw_cells _ _ _ ?cs =>
      destruct (rw_cells_cut usegs _ (AIM + 40) cs 5 OB2') as [OB3 OB4]; cbn [firstn skipn cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in OB3, OB4;
      clear OB2' end.
    replace (AIM + 40 + Z.of_nat 32) with (AIM + 72) in OB4 by lia.
    pose proof OB3 as OB3c.
    lazymatch type of OB3 with rw_cells _ _ _ [?c0; ?c1; ?c2; ?c3; ?c4] =>
      pose proof (rw_cells_merge usegs _ (AIM + 40) [c0] [c1; c2] [c3; c4] OB3) as OB3m; cbn [app cells_size csize Nat.add] in OB3m end.
    lazymatch goal with |- implM _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (HP5 : RHEAP s2' ((sip, ASI, SIDX_BYTES len) :: (imp, AIM, 96) :: LB) mx)
        by (eapply RHEAP_stack_frame; [exact HP4| exact MU4| exact WM4| repeat constructor; cbn; lia]);
      assert (AUX5 : rauxv_ok mx B) by (eapply rauxv_ok_stack_frame; [exact AUX4| exact MU4| exact WM4| repeat constructor; cbn; lia])
    end.
    clear HP4 AUX4.
    eapply implM_bind.
    { eapply (setdepth_proof ONT) with (lo := lo) (B := B) (IMPL := AIM) (pim := imp); try reflexivity; unfold RATP; rewrite ?unsigned_lit by lia;
        first [exact HP5 | exact AUX5 | exact ST4 | exact MI4 | (rewrite errno_lit; unfold RERRNO; exact ERR4) | exact OB3m | exact GOT4
              | (right; left; reflexivity) | (unfold SETDEPTH_STACK, OPNEW_NT_STACK, OPNEW_STACK, RMALLOC_STACK; lia) | lia]. }
    cbv beta. intros [ocp iap] s3' ms3 PO.
    destruct PO as (w0' & w1 & w2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m6 & errv3 & -> & MI6 & ST6 & ERR6 & AUX6 & HPY & FAE3 & SOE3 & RR3).
    destruct RR3 as (AOC & AIA & joc & jia & BRO & BRI & HP6 & BLKO & BLKI & OB5).
    rewrite ?unsigned_lit in ST6 by lia. rewrite ?unsigned_lit in HPY by lia.
    lazymatch goal with |- implM _ _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?r)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 r)) with (Z_to_bv 64 r) by (symmetry; rpc) end.
    lazymatch type of FR4 with rw_cells _ _ _ ?cs =>
      assert (FR6 : rw_cells usegs m6 (bv_unsigned sp + -32) cs)
        by (eapply rheap_pres_x_rw_cells; [exact HPY| exact FR4| left; cbn; lia| cbn; lia]) end.
    apply implM_ret.
    (* [comment removed for export] *)
    do 2 zstep.
    if_cases KE; zify_cond KE; [exfalso; lia|].
    do 6 zstep.
    release_frame FR6 ST6 (bv_unsigned sp).
    apply evt_done. unfold create_post.
    do 15 eexists. exists errv3. split; [reflexivity|].
    split; [exact MI6|]. split; [exact ST6|]. split; [exact ERR6|]. split; [exact AUX6|].
    assert (NB1 : forall a, in_block LB a -> ~ (AIM <= a < AIM + 96)).
    { intros a (b & Hb & Hr) Ha. pose proof (new_block_disj _ _ _ _ _ _ _ HP3 Hb) as D. lia. }
    split.
    { eapply rheap_pres_x_trans.
      { eapply rheap_pres_x_of_munch; [exact MU| exact WM|]. intros a Ha Hc Hx. cbn.
        destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [lia| lia|]. pose proof (LBB b Hb). lia. }
      eapply rheap_pres_x_trans; [eapply rheap_pres_x_of_pres; [exact HPR| lia| intros b Hb; exact Hb]|].
      eapply rheap_pres_x_trans.
      { eapply rheap_pres_x_of_munch; [exact MU2| exact WM2|]. intros a Ha Hc Hx. cbn.
        destruct Hc as [Hc|[Hc|Hb]]; [lia| lia|]. pose proof (NB1 a Hb). destruct Hb as (b & Hb & Hr). pose proof (LBB b Hb). lia. }
      eapply rheap_pres_x_trans.
      { eapply rheap_pres_x_weaken; [exact HPX| lia| intros b Hb; right; exact Hb|]. intros a Hc Hy Hx.
        destruct Hc as [Hc|[Hc|Hb]]; [lia| lia|]. apply (NB1 a Hb). lia. }
      eapply rheap_pres_x_weaken; [exact HPY| lia| intros b Hb; right; right; exact Hb|]. intros a Hc Hy Hx.
      destruct Hc as [Hc|[Hc|Hb]]; [lia| lia|]. apply (NB1 a Hb). lia. }
    split; [congruence|]. split; [congruence|].
    pose proof BRO as (BRO1 & BRO2 & BRO3 & BRO4 & BRO5). pose proof BRI as (BRI1 & BRI2 & BRI3 & BRI4 & BRI5).
    assert (INB : In (imp, AIM, 96) ((sip, ASI, SIDX_BYTES len) :: (imp, AIM, 96) :: LB)) by (right; left; reflexivity).
    assert (DC6 : rw_cells usegs m6 DST [C8 (Z_to_bv 64 AIM)])
      by (eapply rheap_pres_x_rw_cells; [exact HPY| exact DC4| left; cbn; lia| cbn; lia]).
    assert (OB0'' : rw_cells usegs m6 AIM [C8 (Z_to_bv 64 510000)])
      by (eapply rheap_pres_x_rw_cells; [exact HPY| exact OB0'| right; right; exists (imp, AIM, 96); split; [exact INB| cbn; lia]| cbn; lia]).
    lazymatch type of OB1' with rw_cells _ _ _ ?cs =>
      assert (OB1'' : rw_cells usegs m6 (AIM + 8) cs)
        by (eapply rheap_pres_x_rw_cells; [exact HPY| exact OB1'| right; right; exists (imp, AIM, 96); split; [exact INB| cbn; lia]| cbn; lia]) end.
    lazymatch type of OB4 with rw_cells _ _ _ ?cs =>
      assert (OB4' : rw_cells usegs m6 (AIM + 72) cs)
        by (eapply rheap_pres_x_rw_cells; [exact HPY| exact OB4| right; right; exists (imp, AIM, 96); split; [exact INB| cbn; lia]| cbn; lia]) end.
    lazymatch type of BLKS with rw_cells _ _ _ ?cs =>
      assert (BLKS' : rw_cells usegs m6 ASI cs)
        by (eapply rheap_pres_x_rw_cells; [exact HPY| exact BLKS| right; right; exists (sip, ASI, SIDX_BYTES len); split; [left; reflexivity| cbn; lia]| cbn; lia]) end.
    lazymatch type of OB5 with rw_cells _ _ _ [?c0; CB 8 (cells_bytes [?x; ?y]); ?c3; ?c4] =>
      assert (OB5r : rw_cells usegs m6 (AIM + 40) [c0; x; y; c3; c4])
        by (eapply rw_cells_recast; [exact OB5| destruct OB3c as [[W _] _]; cbn in W |- *; tauto| cbn [cells_bytes cbytes]; rewrite <- ?app_assoc; reflexivity| reflexivity]) end.
    lazymatch type of OB0'' with rw_cells _ _ _ ?cs0 =>
    lazymatch type of OB1'' with rw_cells _ _ _ ?cs1 =>
    lazymatch type of OB5r with rw_cells _ _ _ ?cs2 =>
    lazymatch type of OB4' with rw_cells _ _ _ ?cs3 =>
      assert (J : rw_cells usegs m6 AIM (cs0 ++ cs1 ++ cs2 ++ cs3))
        by (apply rw_cells_app_join; [exact OB0''|]; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
            apply rw_cells_app_join; [exact OB1''|]; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
            replace (AIM + 8 + 32) with (AIM + 40) by lia;
            apply rw_cells_app_join; [exact OB5r|]; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
            replace (AIM + 40 + 32) with (AIM + 72) by lia; exact OB4')
    end end end end.
    lazymatch type of J with rw_cells _ _ _ ([_] ++ [_; CB 4 ?q1; _; _; CB 4 ?q2; _] ++ [_; _; CB 6 ?q3; _; _] ++ _) =>
    lazymatch type of BLKS' with rw_cells _ _ _ [_; CB _ ?j1] =>
    lazymatch type of BLKO with rw_cells _ _ _ [CB _ ?j2] =>
    lazymatch type of BLKI with rw_cells _ _ _ [CB _ ?j3] =>
      exists AIM, ASI, AOC, AIA, q1, q2, q3, j1, j2, j3
    end end end end.
    split; [exact BRM|]. split; [exact BRS|]. split; [exact BRO|]. split; [exact BRI|].
    split; [exact HP6|]. split; [exact DC6|].
    split; [exact J|].
    split; [exact BLKS'|]. split; [exact BLKO| exact BLKI].
  Qed.
End Proof.
End CANSEC1.
