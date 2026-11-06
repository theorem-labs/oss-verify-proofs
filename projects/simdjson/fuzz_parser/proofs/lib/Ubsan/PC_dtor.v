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
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Ubsan Require Import PC_kit PC_ukit PC_docdtor PC_impldtor PU_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation mem := (word -> option byte).

Section CANSEC1. Context {rc : runConstT}.
Definition PPARSER_DTOR : Z := 0x26b7c.
Definition PDTOR_STACK : Z := 32 + RFREE_STACK.

(* [comment removed for export] *)
Definition copy_blk (lb : option bptr) (ACP ncp : Z) : list block := match lb with Some p => [(p, ACP, ncp)] | None => [] end.
Definition copy_addr (lb : option bptr) (ACP : Z) : Z := match lb with Some _ => ACP | None => 0 end.
(* [comment removed for export] *)
Definition six_blks (pia poc psi pim ptp psb : bptr) (AIA AOC ASI AIM ATP ASB nia noc nsi nim ntp nsb : Z) : list block :=
  [(pia, AIA, nia); (poc, AOC, noc); (psi, ASI, nsi); (pim, AIM, nim); (ptp, ATP, ntp); (psb, ASB, nsb)].

Definition pdtor_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB0 : list block) (lo B P : Z) (m : mem) (r : unit) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' (errno_addr tp) [C4 errv'] /\ rauxv_ok m' B
    /\ rheap_pres_x LB0 (bv_unsigned sp) (P + 8) 64 m m'
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ RHEAP s' LB0 m'
    /\ stk usegs m' P (P + 80).

Definition pdtor_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB0 : list block) (lb : option bptr) (pia poc psi pim ptp psb : bptr)
         (ACP AIA AOC ASI AIM ATP ASB ncp nia noc nsi nim ntp nsb lo B P : Z) (errv : word),
  RHEAP s (copy_blk lb ACP ncp ++ six_blks pia poc psi pim ptp psb AIA AOC ASI AIM ATP ASB nia noc nsi nim ntp nsb ++ LB0) m ->
  72 <= nim ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk usegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - PDTOR_STACK ->
  rw_cells usegs m (errno_addr tp) [C4 errv] ->
  mem_inv usegs m ->
  tp = Z_to_bv 64 RATP ->
  rw_cells usegs m PVTAB_DOM vtab_dom_cells ->
  rw_cells usegs m (P + 8) [C8 (Z_to_bv 64 AIM)] ->
  rw_cells usegs m (P + 24) [C8 (Z_to_bv 64 ATP); C8 (Z_to_bv 64 ASB)] ->
  rw_cells usegs m (P + 64) [C8 (Z_to_bv 64 (copy_addr lb ACP))] ->
  bv_unsigned sp <= P -> P + 72 <= B -> stk usegs m P (P + 80) ->
  rw_cells usegs m AIM [C8 (Z_to_bv 64 PVTAB_DOM)] -> rw_cells usegs m (AIM + 16) [C8 (Z_to_bv 64 ASI)] ->
  rw_cells usegs m (AIM + 56) [C8 (Z_to_bv 64 AOC); C8 (Z_to_bv 64 AIA)] ->
  a0 = Z_to_bv 64 P ->
  implM usegs (HarnessP.parser_dtor raw_free (psb, ptp, (pim, psi, poc, pia), lb)) s
        (pdtor_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB0 lo B P m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 PPARSER_DTOR) fc None m (seg_rom usegs)).

(* [comment removed for export] *)
Lemma six_nodup : forall pia poc psi pim ptp psb AIA AOC ASI AIM ATP ASB nia noc nsi nim ntp nsb LB0,
  List.NoDup (map blk_id (six_blks pia poc psi pim ptp psb AIA AOC ASI AIM ATP ASB nia noc nsi nim ntp nsb ++ LB0)) ->
  psb <> ptp /\ List.NoDup [pim; psi; poc; pia].
Proof.
  intros until LB0. intros ND. cbn [six_blks app map blk_id fst] in ND.
  apply NoDup_cons_iff in ND as [N1 ND]. apply NoDup_cons_iff in ND as [N2 ND]. apply NoDup_cons_iff in ND as [N3 ND].
  apply NoDup_cons_iff in ND as [N4 ND]. apply NoDup_cons_iff in ND as [N5 _].
  cbn [In] in N1, N2, N3, N4, N5. split; [intros E; subst; tauto|].
  repeat constructor; cbn [In]; intros H; repeat destruct H as [H|H]; subst; tauto.
Qed.

Lemma nodup_rm_mid : forall L1 b L2, List.NoDup (map blk_id (L1 ++ b :: L2)) -> List.NoDup (map blk_id (L1 ++ L2)).
Proof. intros L1 b L2 ND. rewrite map_app in ND |- *. cbn [map] in ND. apply NoDup_remove in ND as [ND _]. exact ND. Qed.
Lemma lb_remove_hd_nd : forall p A n L, List.NoDup (map blk_id ((p, A, n) :: L)) ->
  lb_remove p ((p, A, n) :: L) = L /\ List.NoDup (map blk_id L).
Proof.
  intros p A n L ND. split; [exact (lb_remove_hd' (p, A, n) L ND)|].
  cbn [map] in ND. apply NoDup_cons_iff in ND as [_ ND]. exact ND.
Qed.

(* [comment removed for export] *)
Ltac lit_if_pc := lazymatch goal with |- evt _ _ (MS ?R ?F (if ?c then ?x else ?y) ?fc ?rv ?mm ?ro) =>
   let v := eval vm_compute in c in
   lazymatch v with true => change (if c then x else y) with x | false => change (if c then x else y) with y end end.

Section Proof.
  Hypothesis ODA : opdelete_arr_stmt.
  Hypothesis OD : opdelete_stmt.

  (* [comment removed for export] *)
  Lemma pdtor_tail : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB0 : list block) (pia poc psi pim ptp psb : bptr)
         (AIA AOC ASI AIM ATP ASB nia noc nsi nim ntp nsb lo B P : Z) (errv : word)
         (ra1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m1 : mem) (s1' : PState),
    RHEAP s1' (six_blks pia poc psi pim ptp psb AIA AOC ASI AIM ATP ASB nia noc nsi nim ntp nsb ++ LB0) m1 ->
    72 <= nim ->
    rauxv_ok m1 B -> bv_unsigned sp <= B ->
    stk usegs m1 lo (bv_unsigned sp + -16) -> ATOP <= lo -> lo <= bv_unsigned sp - PDTOR_STACK ->
    rw_cells usegs m1 (bv_unsigned sp + -16) [C8 s0; C8 ra] ->
    rw_cells usegs m1 RERRNO [C4 errv] ->
    mem_inv usegs m1 ->
    tp = Z_to_bv 64 RATP ->
    rw_cells usegs m1 PVTAB_DOM vtab_dom_cells ->
    rw_cells usegs m1 (P + 8) [C8 (Z_to_bv 64 AIM)] ->
    rw_cells usegs m1 (P + 24) [C8 (Z_to_bv 64 ATP); C8 (Z_to_bv 64 ASB)] ->
    bv_unsigned sp <= P -> P + 72 <= B -> stk usegs m1 P (P + 80) ->
    rw_cells usegs m1 AIM [C8 (Z_to_bv 64 PVTAB_DOM)] -> rw_cells usegs m1 (AIM + 16) [C8 (Z_to_bv 64 ASI)] ->
    rw_cells usegs m1 (AIM + 56) [C8 (Z_to_bv 64 AOC); C8 (Z_to_bv 64 AIA)] ->
    rheap_pres_x LB0 (bv_unsigned sp) (P + 8) 64 m m1 -> ps_fa s1' = ps_fa s -> ps_so s1' = ps_so s ->
    implM usegs (HarnessP.doc_dtor raw_free psb ptp ;;; HarnessP.impl_dtor raw_free (pim, psi, poc, pia)) s1'
          (pdtor_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB0 lo B P m)
          (MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 (Z_to_bv 64 P) s1 a0 a1 a2 a3 a4 a5 a6 a7
                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x26b9c) fc None m1 (seg_rom usegs)).
  Proof.
    intros until s1'. intros HP NIM AUX SPB ST LOA LOS FR ERR MI TP VT PIM PDOC PSP PTOP PSTK IM0 IM16 IM56 PRE FAE0 SOE0.
    destruct (stk_split usegs _ P (P + 24) (P + 80) PSTK ltac:(lia)) as [_ PSTK2]. destruct (stk_split usegs _ (P + 24) (P + 40) (P + 80) PSTK2 ltac:(lia)) as [DSTK _].
    clear PSTK2.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    unfold PDTOR_STACK, RFREE_STACK in LOS. atop_facts.
    subst tp. unfold PVTAB_DOM, vtab_dom_cells in VT. unfold PVTAB_DOM in IM0.
    pose proof (RMalloc_ifaceP.RHEAP_blocks_nodup_proof _ _ _ HP) as ND.
    destruct (six_nodup _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ND) as [NEsbtp ND4].
    assert (LBB : forall b, In b (six_blks pia poc psi pim ptp psb AIA AOC ASI AIM ATP ASB nia noc nsi nim ntp nsb ++ LB0) ->
              blk_addr b + blk_size b <= ATOP)
      by (intros b Hb; destruct (RMalloc_ifaceP.RHEAP_block_range_proof _ _ _ b HP Hb) as (_ & _ & _ & R4 & _); exact R4).
    assert (INM0 : In (pim, AIM, nim) (six_blks pia poc psi pim ptp psb AIA AOC ASI AIM ATP ASB nia noc nsi nim ntp nsb ++ LB0))
      by (cbn; tauto).
    pose proof (RMalloc_ifaceP.RHEAP_block_range_proof _ _ _ _ HP INM0) as (BM1 & BM2 & BM3 & BM4 & BM5). cbn [blk_addr blk_size fst snd] in *.
    (* [comment removed for export] *)
    apply implM_from_evt.
    do 2 zstep.
    apply evt_done.
    eapply implM_bind.
    { eapply (docdtor_proof ODA) with (lo := lo) (B := B) (DOC := P + 24) (ASB := ASB) (ATP := ATP) (nsb := nsb) (ntp := ntp);
        try reflexivity; unfold RATP; rewrite ?unsigned_lit by lia;
        first [exact HP | (cbn; tauto) | exact NEsbtp | exact AUX | exact ST | exact MI | (rewrite errno_lit; exact ERR) | exact PDOC
              | (replace (P + 24 + 16) with (P + 40) by lia; exact DSTK)
              | (unfold DOCDTOR_STACK, RFREE_STACK; lia) | lia]. }
    cbv beta. intros [] s2' ms2 PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m3 & errv3 & -> & MI3 & ST3 & ERR3 & AUX3 & HPX & FAE & SOE & HP3 & DSTK3).
    rewrite ?unsigned_lit in ST3 by lia. rewrite ?unsigned_lit in HPX by lia. rewrite errno_lit in ERR3. unfold RERRNO in ERR3.
    assert (PSTK3 : stk usegs m3 P (P + 80)) by (eapply stk_of_x_stk; [exact HPX| exact PSTK| exact DSTK3| lia| lia| lia]).
    clear PSTK DSTK DSTK3.
    lazymatch goal with |- implM _ _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?r)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 r)) with (Z_to_bv 64 r) by (symmetry; rpc) end.
    (* [comment removed for export] *)
    assert (E2 : lb_remove ptp (lb_remove psb (six_blks pia poc psi pim ptp psb AIA AOC ASI AIM ATP ASB nia noc nsi nim ntp nsb ++ LB0))
                 = [(pia, AIA, nia); (poc, AOC, noc); (psi, ASI, nsi); (pim, AIM, nim)] ++ LB0).
    { assert (E1 : lb_remove psb (six_blks pia poc psi pim ptp psb AIA AOC ASI AIM ATP ASB nia noc nsi nim ntp nsb ++ LB0)
                   = [(pia, AIA, nia); (poc, AOC, noc); (psi, ASI, nsi); (pim, AIM, nim); (ptp, ATP, ntp)] ++ LB0)
        by exact (lb_remove_mid [(pia, AIA, nia); (poc, AOC, noc); (psi, ASI, nsi); (pim, AIM, nim); (ptp, ATP, ntp)] (psb, ASB, nsb) LB0 ND).
      rewrite E1.
      exact (lb_remove_mid [(pia, AIA, nia); (poc, AOC, noc); (psi, ASI, nsi); (pim, AIM, nim)] (ptp, ATP, ntp) LB0
               (nodup_rm_mid [(pia, AIA, nia); (poc, AOC, noc); (psi, ASI, nsi); (pim, AIM, nim); (ptp, ATP, ntp)] (psb, ASB, nsb) LB0 ND)). }
    rewrite E2 in HP3, HPX.
    change ([(pia, AIA, nia); (poc, AOC, noc); (psi, ASI, nsi); (pim, AIM, nim)] ++ LB0)
      with ((pia, AIA, nia) :: (poc, AOC, noc) :: (psi, ASI, nsi) :: (pim, AIM, nim) :: LB0) in HP3, HPX.
    assert (INM3 : In (pim, AIM, nim) ((pia, AIA, nia) :: (poc, AOC, noc) :: (psi, ASI, nsi) :: (pim, AIM, nim) :: LB0)) by (cbn; tauto).
    lazymatch type of FR with rw_cells _ _ _ ?cs =>
      assert (FR3 : rw_cells usegs m3 (bv_unsigned sp + -16) cs) by (eapply rheap_pres_x_rw_cells; [exact HPX| exact FR| left; cbn; lia| cbn; lia]) end.
    assert (PIM3 : rw_cells usegs m3 (P + 8) [C8 (Z_to_bv 64 AIM)]) by (eapply rheap_pres_x_rw_cells; [exact HPX| exact PIM| left; cbn; lia| cbn; lia]).
    lazymatch type of IM0 with rw_cells _ _ _ ?cs =>
      assert (IM0' : rw_cells usegs m3 AIM cs)
        by (eapply rheap_pres_x_rw_cells; [exact HPX| exact IM0| right; right; exists (pim, AIM, nim); split; [exact INM3| cbn; lia]| cbn; lia]) end.
    lazymatch type of IM56 with rw_cells _ _ _ ?cs =>
      assert (IM56' : rw_cells usegs m3 (AIM + 56) cs)
        by (eapply rheap_pres_x_rw_cells; [exact HPX| exact IM56| right; right; exists (pim, AIM, nim); split; [exact INM3| cbn; lia]| cbn; lia]) end.
    lazymatch type of IM16 with rw_cells _ _ _ ?cs =>
      assert (IM16' : rw_cells usegs m3 (AIM + 16) cs)
        by (eapply rheap_pres_x_rw_cells; [exact HPX| exact IM16| right; right; exists (pim, AIM, nim); split; [exact INM3| cbn; lia]| cbn; lia]) end.
    lazymatch type of VT with rw_cells _ _ _ ?cs =>
      assert (VT3 : rw_cells usegs m3 0x7c830 cs)
        by (eapply rheap_pres_x_rw_cells; [exact HPX| exact VT| right; left; unfold RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP; cbn; lia| cbn; lia]) end.
    clear FR PIM IM0 IM16 IM56 VT PDOC ST MI ERR AUX.
    (* [comment removed for export] *)
    apply implM_from_evt.
    pose proof (munch_refl [(lo, bv_unsigned sp); (P + 8, P + 72)] m3) as MU3. pose proof (wmono_refl usegs m3) as WM3.
    do 3 zstep.
    if_cases K1; zify_cond K1; [exfalso; lia|].
    (* [comment removed for export] *)
    do 2 zstep.
    if_cases KA; zify_cond KA; [exfalso; exact (KA (land7_of_mod16 AIM BM2))|].
    do 6 zstep.
    release_frame FR3 ST3 (bv_unsigned sp).
    apply evt_done.
    lazymatch goal with |- implM _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (HP5 : RHEAP s2' ((pia, AIA, nia) :: (poc, AOC, noc) :: (psi, ASI, nsi) :: (pim, AIM, nim) :: LB0) mx)
        by (eapply RHEAP_stack_frame; [exact HP3| exact MU3| exact WM3| repeat constructor; cbn; lia]);
      assert (AUX5 : rauxv_ok mx B) by (eapply rauxv_ok_stack_frame; [exact AUX3| exact MU3| exact WM3| repeat constructor; cbn; lia])
    end.
    pose proof (RMalloc_ifaceP.RHEAP_blocks_nodup_proof _ _ _ HP5) as ND5.
    eapply implM_mono.
    { eapply (impldtor_proof ODA OD) with (lo := lo) (B := B) (AIM := AIM) (ASI := ASI) (AOC := AOC) (AIA := AIA)
        (nim := nim) (nsi := nsi) (noc := noc) (nia := nia);
        try reflexivity; unfold RATP; rewrite ?unsigned_lit by lia;
        first [exact HP5 | (cbn; tauto) | exact ND4 | exact NIM | exact AUX5 | exact ST3 | exact MI3 | (rewrite errno_lit; unfold RERRNO; exact ERR3)
              | exact IM0' | exact IM16' | exact IM56' | (unfold IMPLDTOR_STACK, RFREE_STACK; lia) | lia]. }
    cbv beta. intros [] s4' ms4 PO.
    destruct PO as (x0 & x1 & x2 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & x3 & x4 & x5 & x6 & m5 & errv5 & -> & MI5 & ST5 & ERR5 & AUX5' & HPR5 & FAE5 & SOE5 & HP5').
    assert (E4 : impl_rm pim psi poc pia ((pia, AIA, nia) :: (poc, AOC, noc) :: (psi, ASI, nsi) :: (pim, AIM, nim) :: LB0) = LB0).
    { unfold impl_rm.
      destruct (lb_remove_hd_nd _ _ _ _ ND5) as [R1 N1]. rewrite R1.
      destruct (lb_remove_hd_nd _ _ _ _ N1) as [R2 N2]. rewrite R2.
      destruct (lb_remove_hd_nd _ _ _ _ N2) as [R3 N3]. rewrite R3.
      destruct (lb_remove_hd_nd _ _ _ _ N3) as [R4 _]. exact R4. }
    rewrite E4 in HPR5, HP5'.
    unfold pdtor_post. do 16 eexists. exists errv5. split; [reflexivity|].
    split; [exact MI5|]. split; [exact ST5|]. split; [first [exact ERR5 | (rewrite errno_lit; exact ERR5)]|]. split; [exact AUX5'|].
    assert (LBB0 : forall b, In b LB0 -> blk_addr b + blk_size b <= ATOP) by (intros b Hb; apply LBB; apply in_or_app; right; exact Hb).
    split.
    { eapply rheap_pres_x_trans; [exact PRE|].
      eapply rheap_pres_x_trans.
      { eapply rheap_pres_x_weaken; [exact HPX| lia| intros b Hb; cbn; tauto| intros a _ Hy Hx; apply Hy; lia]. }
      eapply rheap_pres_x_trans.
      { eapply rheap_pres_x_of_munch; [exact MU3| exact WM3|]. intros a Ha Hc Hx. cbn.
        destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [lia| lia|]. pose proof (LBB0 b Hb). lia. }
      eapply rheap_pres_x_of_pres; [exact HPR5| lia| intros b Hb; exact Hb]. }
    split; [congruence|]. split; [congruence|]. split; [exact HP5'|].
    lazymatch goal with D : stk usegs _ P (P + 80) |- _ => eapply rheap_pres_stk; [exact HPR5| exact D| lia] end.
  Qed.

  Theorem pdtor_proof : pdtor_stmt.
  Proof.
    unfold pdtor_stmt. intros until errv. intros HP NIM AUX SPB ST LOA LOS ERR MI TP VT PIM PDOC PCP PSP PTOP PSTK IM0 IM16 IM56 A0.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    unfold PDTOR_STACK, RFREE_STACK in LOS. atop_facts.
    pose proof (RMalloc_ifaceP.RHEAP_blocks_nodup_proof _ _ _ HP) as ND.
    assert (LBB : forall b, In b (copy_blk lb ACP ncp ++ six_blks pia poc psi pim ptp psb AIA AOC ASI AIM ATP ASB nia noc nsi nim ntp nsb ++ LB0) ->
              blk_addr b + blk_size b <= ATOP)
      by (intros b Hb; destruct (RMalloc_ifaceP.RHEAP_block_range_proof _ _ _ b HP Hb) as (_ & _ & _ & R4 & _); exact R4).
    assert (OUTW : forall a, 0 <= a < 2^64 -> rclient_addr LB0 (bv_unsigned sp) a -> ~ (P + 8 <= a < P + 8 + 64) ->
              outside [(lo, bv_unsigned sp); (P + 8, P + 72)] a).
    { intros a Ha Hc Hx. cbn. destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [lia| lia|].
      assert (Hb' : In b (copy_blk lb ACP ncp ++ six_blks pia poc psi pim ptp psb AIA AOC ASI AIM ATP ASB nia noc nsi nim ntp nsb ++ LB0))
        by (apply in_or_app; right; apply in_or_app; right; exact Hb).
      pose proof (LBB b Hb'). lia. }
    subst tp. rewrite errno_lit in ERR. unfold RERRNO in ERR. unfold PVTAB_DOM, vtab_dom_cells in VT. unfold PVTAB_DOM in IM0.
    assert (INM0 : In (pim, AIM, nim) (copy_blk lb ACP ncp ++ six_blks pia poc psi pim ptp psb AIA AOC ASI AIM ATP ASB nia noc nsi nim ntp nsb ++ LB0))
      by (apply in_or_app; right; cbn; tauto).
    pose proof (RMalloc_ifaceP.RHEAP_block_range_proof _ _ _ _ HP INM0) as (BM1 & BM2 & BM3 & BM4 & BM5). cbn [blk_addr blk_size fst snd] in *.
    unfold HarnessP.parser_dtor.
    apply implM_from_evt.
    pose proof (munch_refl [(lo, bv_unsigned sp); (P + 8, P + 72)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    carve_frame 16%nat ST.
    subst a0. unfold PPARSER_DTOR.
    destruct lb as [pcp|]; cbn [copy_blk copy_addr app HarnessP.odelete] in *.
    - (* [comment removed for export] *)
      assert (INC : In (pcp, ACP, ncp) ((pcp, ACP, ncp) :: six_blks pia poc psi pim ptp psb AIA AOC ASI AIM ATP ASB nia noc nsi nim ntp nsb ++ LB0))
        by (left; reflexivity).
      pose proof (RMalloc_ifaceP.RHEAP_block_range_proof _ _ _ _ HP INC) as (BC1 & BC2 & BC3 & BC4 & BC5). cbn [blk_addr blk_size fst snd] in *.
      do 7 zstep.
      if_cases K0; zify_cond K0; [exfalso; lia|].
      do 1 zstep.
      apply evt_done.
      lazymatch goal with |- implM _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
        assert (HP1 : RHEAP s ((pcp, ACP, ncp) :: six_blks pia poc psi pim ptp psb AIA AOC ASI AIM ATP ASB nia noc nsi nim ntp nsb ++ LB0) mx)
          by (eapply RHEAP_stack_frame; [exact HP| exact MU| exact WM| repeat constructor; cbn; lia]);
        assert (AUX1 : rauxv_ok mx B) by (eapply rauxv_ok_stack_frame; [exact AUX| exact MU| exact WM| repeat constructor; cbn; lia])
      end.
      eapply implM_bind.
      { eapply ODA with (lo := lo) (B := B) (A := ACP) (n := ncp); try reflexivity; unfold RATP; rewrite ?unsigned_lit by lia;
          first [exact HP1 | exact INC | exact AUX1 | exact ST | exact MI | (rewrite errno_lit; unfold RERRNO; exact ERR)
                | (unfold RFREE_STACK; lia) | lia]. }
      cbv beta. intros [] s1' ms1 PO.
      destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & -> & MI2 & ST2 & ERR2 & AUX2 & HPR & FAE & SOE & HP2).
      destruct (lb_remove_hd_nd _ _ _ _ ND) as [E0 _]. rewrite E0 in HP2, HPR.
      rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in HPR by lia.
      lazymatch goal with |- implM _ _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?r)) _ _ _ _) =>
        replace (ret_pc (Z_to_bv 64 r)) with (Z_to_bv 64 r) by (symmetry; rpc) end.
      assert (INM : In (pim, AIM, nim) (six_blks pia poc psi pim ptp psb AIA AOC ASI AIM ATP ASB nia noc nsi nim ntp nsb ++ LB0)) by (cbn; tauto).
      lazymatch goal with FR : rw_cells usegs _ (bv_unsigned sp + -16) ?cs |- _ =>
        assert (FR2 : rw_cells usegs m2 (bv_unsigned sp + -16) cs) by (eapply rheap_pres_rw_cells; [exact HPR| exact FR| left; cbn; lia]); clear FR end.
      assert (PIM2 : rw_cells usegs m2 (P + 8) [C8 (Z_to_bv 64 AIM)]) by (eapply rheap_pres_rw_cells; [exact HPR| exact PIM| left; cbn; lia]).
      assert (PDOC2 : rw_cells usegs m2 (P + 24) [C8 (Z_to_bv 64 ATP); C8 (Z_to_bv 64 ASB)]) by (eapply rheap_pres_rw_cells; [exact HPR| exact PDOC| left; cbn; lia]).
      lazymatch goal with D : stk usegs _ P (P + 80) |- _ =>
        assert (PSTK2 : stk usegs m2 P (P + 80)) by (eapply rheap_pres_stk; [exact HPR| exact D| lia]); clear D end.
      lazymatch type of IM0 with rw_cells _ _ _ ?cs =>
        assert (IM0' : rw_cells usegs m2 AIM cs)
          by (eapply rheap_pres_rw_cells; [exact HPR| exact IM0| right; right; exists (pim, AIM, nim); split; [exact INM| cbn; lia]]) end.
      lazymatch type of IM56 with rw_cells _ _ _ ?cs =>
        assert (IM56' : rw_cells usegs m2 (AIM + 56) cs)
          by (eapply rheap_pres_rw_cells; [exact HPR| exact IM56| right; right; exists (pim, AIM, nim); split; [exact INM| cbn; lia]]) end.
      lazymatch type of IM16 with rw_cells _ _ _ ?cs =>
        assert (IM16' : rw_cells usegs m2 (AIM + 16) cs)
          by (eapply rheap_pres_rw_cells; [exact HPR| exact IM16| right; right; exists (pim, AIM, nim); split; [exact INM| cbn; lia]]) end.
      lazymatch type of VT with rw_cells _ _ _ ?cs =>
        assert (VT2 : rw_cells usegs m2 PVTAB_DOM cs)
          by (eapply rheap_pres_rw_cells; [exact HPR| exact VT| right; left; unfold PVTAB_DOM, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP; cbn; lia]) end.
      rewrite errno_lit in ERR2.
      assert (PRE : rheap_pres_x LB0 (bv_unsigned sp) (P + 8) 64 m m2).
      { eapply rheap_pres_x_trans; [eapply rheap_pres_x_of_munch; [exact MU| exact WM| exact OUTW]|].
        eapply rheap_pres_x_of_pres; [exact HPR| lia| intros b Hb; apply in_or_app; right; exact Hb]. }
      eapply (pdtor_tail ra sp gp (Z_to_bv 64 RATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s LB0 pia poc psi pim ptp psb
                AIA AOC ASI AIM ATP ASB nia noc nsi nim ntp nsb lo B P errv); try eassumption; try reflexivity; congruence.
    - (* [comment removed for export] *)
      do 7 zstep.
      first [lit_if_pc | idtac].
      apply evt_done.
      apply implM_retb.
      lazymatch goal with |- implM _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
        assert (HP1 : RHEAP s (six_blks pia poc psi pim ptp psb AIA AOC ASI AIM ATP ASB nia noc nsi nim ntp nsb ++ LB0) mx)
          by (eapply RHEAP_stack_frame; [exact HP| exact MU| exact WM| repeat constructor; cbn; lia]);
        assert (AUX1 : rauxv_ok mx B) by (eapply rauxv_ok_stack_frame; [exact AUX| exact MU| exact WM| repeat constructor; cbn; lia])
      end.
      eapply (pdtor_tail ra sp gp (Z_to_bv 64 RATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s LB0 pia poc psi pim ptp psb
                AIA AOC ASI AIM ATP ASB nia noc nsi nim ntp nsb lo B P errv); try eassumption; try reflexivity.
      eapply rheap_pres_x_of_munch; [exact MU| exact WM| exact OUTW].
  Qed.
End Proof.
End CANSEC1.
