(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import Stdio_pure.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Ubsan Require Import UImg.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Ubsan Require Import RMallocRep RMallocTree RMalloc_iface ROpNew_iface.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Ubsan Require RMalloc_ifaceP RDriver_facts.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Prelim Monad Stdio Malloc PState HarnessM ProgP.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Plain Require Import PM_model.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Ubsan Require Import PAtexit_cells RunDraw PU_iface PM_kit PM_iface UM_guards.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation mem := (word -> option byte).

Section CANSEC1. Context {rc : runConstT}.
Definition PJOIN : Z := 0x3c088.         (* [comment removed for export] *)

(* [comment removed for export] *)
Definition join_rel (s0 : PState) (LB0 : list block) (m0 : mem) (s : PState) (LB : list block) (m : mem) (SP : Z) : Prop :=
  harness_pres LB0 SP m0 m
  /\ ps_so s = ps_so s0
  /\ (forall b, In b LB0 -> In b LB)
  /\ match ps_fa s0 with
     | Some _ => LB = LB0 /\ ps_fa s = ps_fa s0
     | None => exists p V, LB = (p, V, 8) :: LB0 /\ ps_fa s = Some p
     end.

Lemma implM_get_l : forall {B} (k : PState -> Monad.M PState B) s Q ms,
  implM usegs (k s) s Q ms -> implM usegs (mbind mget k) s Q ms.
Proof. intros. exact H. Qed.

Section Proof.
  Hypothesis LAM : lam_stmt.
  Hypothesis OD : opdelete_stmt.

  (* [comment removed for export] *)
  Lemma fuzz_join : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)       (* [comment removed for export] *)
      (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 xs2 xs3 xs5 xs6 xs7 xs8 t3 t4 t5 t6 : word)         (* [comment removed for export] *)
      (F : bvmap 5 word) (fc : bv 32) (m m0 : mem) (s s0' : PState) (LB LB0 : list block)
      (D : Z) (pl : list Z) (AB lo : Z) (errv : word) (p : bptr) (V : Z),
    RHEAP s LB m -> In (p, V, 8) LB -> ps_fa s = Some p ->
    join_rel s0' LB0 m0 s LB m (bv_unsigned sp) ->
    bytes_at usegs m D (map (Z_to_bv 8) pl) -> Forall (fun c => 0 <= c < 256) pl ->
    rclient_range LB0 (bv_unsigned sp) D (zlength pl) ->
    0 < D -> D + zlength pl <= ATOP -> zlength pl < 2^26 ->
    client_img m ->
    rw_cells usegs m V [C8 (Z_to_bv 64 PFALLBACK)] ->
    rw_cells usegs m PVEC_GUARD guard1 ->
    rw_cells usegs m PVEC [C8 (Z_to_bv 64 V); C8 (Z_to_bv 64 (V + 8)); C8 (Z_to_bv 64 (V + 8))] ->
    rw_cells usegs m PFALLBACK [C8 (Z_to_bv 64 PFALLBACK_VT)] ->
    patexit 3 PDTOR_THUNK PVEC m ->
    rauxv_ok m AB -> bv_unsigned sp <= AB ->
    stk usegs m lo (bv_unsigned sp + -80) -> ATOP <= lo -> lo <= bv_unsigned sp - PHARNESS_STACK ->
    rw_cells usegs m (bv_unsigned sp + -80) [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells usegs m (errno_addr tp) [C4 errv] ->
    mem_inv usegs m -> frm0 fc ->
    tp = Z_to_bv 64 RATP -> bv_unsigned sp mod 16 = 0 ->
    implM usegs (HarnessM.minify_call raw_malloc raw_free ProgP.new_handler pl ;;; mret 0) s
          (fuzz_oneU_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0' LB0 AB lo m0)
          (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -192)) gp tp t0 t1 t2 (Z_to_bv 64 (zlength pl)) (Z_to_bv 64 D) a0 a1 a2 a3 a4 a5 a6 a7
                   xs2 xs3 (Z_to_bv 64 PVEC_GUARD) xs5 xs6 xs7 xs8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 PJOIN) fc None m (seg_rom usegs)).
  Proof.
    intros until V. intros HP PIN FA JR DAT PLB DCR D0 DTOP NLT CI VV GU PV FB PAT AUX SPB ST LOA LOS FRA ERR MI FZ TP SPA.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    unfold PHARNESS_STACK in LOS. atop_facts.
    subst tp. rewrite errno_lit in ERR. unfold RERRNO in ERR.
    set (n := zlength pl) in *.
    assert (N0 : 0 <= n) by (unfold n, zlength; lia).
    destruct JR as (HPRE & SOE0 & LBSUB & FAREL).
    destruct CI as (CI1 & CI2 & CI3 & CI4 & CI5). unfold UJT in CI5. unfold guard1, PVEC_GUARD in GU. unfold PVEC in PV, PAT. unfold PFALLBACK in FB, VV.
    unfold patexit, patx_table, PCALL_THUNK, PAEF_GUARD, PDTOR_THUNK in PAT. destruct PAT as (AT1 & AT2 & AT3 & AT4 & AT5).
    pose proof (RMalloc_ifaceP.RHEAP_block_range_proof s LB m) as LBR.
    assert (LBB : forall b, In b LB -> blk_addr b + blk_size b <= ATOP) by (intros b Hb; destruct (LBR b HP Hb) as (_ & _ & _ & R4 & _); exact R4).
    assert (LBPOS : forall b, In b LB -> 0 < blk_addr b) by (intros b Hb; destruct (LBR b HP Hb) as (R1 & _); exact R1).
    pose proof (LBR _ HP PIN) as (VB1 & VB2 & _ & VB4 & VB5). cbn [blk_addr blk_size fst snd] in VB1, VB2, VB4, VB5.
    clear LBR.
    assert (BSL : Z.of_nat (length (map (Z_to_bv 8) pl)) = n) by (rewrite length_map; reflexivity).
    assert (DLO : D + n <= lo \/ bv_unsigned sp <= D).
    { destruct DCR as [H|[H|(b0 & Hb & Hr)]]; [right; exact H| left; lia| left; pose proof (LBB b0 (LBSUB b0 Hb)); lia]. }
    (* [comment removed for export] *)
    assert (OUTW : forall LB1 SP0 a, 0 <= a < 2^64 -> rclient_addr LB1 SP0 a -> bv_unsigned sp <= SP0 ->
              (forall b, In b LB1 -> blk_addr b + blk_size b <= ATOP) -> outside [(lo, bv_unsigned sp)] a).
    { intros LB1 SP0 a Ha Hc HS HB0. cbn. destruct Hc as [Hc|[Hc|(b0 & Hb & Hr)]]; [lia| unfold ralloc_static in Hc; lia|].
      specialize (HB0 b0 Hb). lia. }
    (* [comment removed for export] *)
    eapply (implM_bind usegs _ _ s (fun _ s' ms' => evt usegs (fuzz_oneU_post ra sp gp (Z_to_bv 64 RATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0' LB0 AB lo m0 0 s') ms')).
    2:{ intros u s' ms' H. apply implM_ret. exact H. }
    apply minify_call_of_lam.
    apply implM_from_evt.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    carve_frame 16%nat ST.                                       (* [comment removed for export] *)
    rename FR into FRC.
    carve_frame 24%nat ST.                                       (* [comment removed for export] *)
    rename FR into FRR.
    carve_frame 72%nat ST.                                       (* [comment removed for export] *)
    rename FR into FRL.
    unfold PJOIN, PVEC_GUARD.
    zstep.                                                       (* [comment removed for export] *)
    zstep. zstep. zstep.                                         (* [comment removed for export] *)
    zstep. if_cases GA1; zify_cond GA1; [exfalso; ubalign GA1; lia|].            (* [comment removed for export] *)
    zstep.                                                       (* [comment removed for export] *)
    zstep. zstep. if_cases GA2; zify_cond GA2; [exfalso; ubalign GA2; lia|].     (* [comment removed for export] *)
    zstep. if_cases GA3; zify_cond GA3; [exfalso; lia|].                          (* [comment removed for export] *)
    zstep.                                                       (* [comment removed for export] *)
    zstep. zstep. zstep.                                         (* [comment removed for export] *)
    apply evt_done.
    lazymatch goal with |- implM _ _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    rename FRC into CC.
    assert (HP1 : RHEAP s LB m1) by (eapply RHEAP_stack_frame; [exact HP| exact MU| exact WM| repeat constructor; cbn; lia]).
    assert (AUX1 : rauxv_ok m1 AB) by (eapply rauxv_ok_stack_frame; [exact AUX| exact MU| exact WM| repeat constructor; cbn; lia]).
    hide MU. hide WM.
    eapply implM_bind.
    { eapply LAM with (lo := lo) (B := AB) (R := bv_unsigned sp + -120) (C := bv_unsigned sp + -96) (D := D) (pl := pl);
        change (zlength pl) with n; try (apply eq_refl); rewrite ?unsigned_lit by lia;
        first [ exact HP1 | exact AUX1 | exact ST | exact MI | (rewrite errno_lit; exact ERR) | (split; [exact CI1|]; split; [exact CI2|]; split; [exact CI3|]; split; [exact CI4| exact CI5]) | (unfold PFALLBACK, PFALLBACK_VT; exact FB)
              | exact FRR | exact CC | exact DAT | exact PLB
              | (eapply rclient_range_mono; [exact LBSUB|]; eapply rclient_range_sp; [exact DCR| lia])
              | (unfold LAM_STACK, ASSIGN_STACK, OPNEW_STACK, RMALLOC_STACK; lia) | (unfold PFALLBACK; apply eq_refl) | (f_equal; lia) | lia
              | match goal with |- ?G => idtac "LEFT:" G end ]. all: fail. }
    cbv beta. intros b' sv msv PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv2 & -> & MI2 & ST2 & ERR2 & AUX2 & HPX & FAE & SOE & KL).
    rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in HPX by lia. rewrite errno_lit in ERR2. unfold RERRNO in ERR2.
    ret_lit.
    trx HPX. clear ST MI ERR AUX1 HP1 DAT.
    (* [comment removed for export] *)
    apply implM_from_evt.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m2) as MU2. pose proof (wmono_refl usegs m2) as WM2.
    (* [comment removed for export] *)
    unfold lam_K in KL. change (zlength pl) with n in KL. cbv zeta in KL.
    destruct b' as [p'|].
    - destruct KL as (A' & n' & e' & HP2 & NP' & BR' & HE' & RC2). pose proof BR' as (BR1 & BR2 & BR3 & BR4 & BR5). unfold vec_cells in RC2.
      zstep. zstep. if_cases GB; zify_cond GB; [exfalso; rewrite ?unsigned_lit in GB by lia; lia|].   (* [comment removed for export] *)
      zstep.
      zstep. first [ lit_if | (if_cases K0; zify_cond K0; [clear K0| exfalso; lia]) ].
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.                                (* [comment removed for export] *)
      zstep.                                                     (* [comment removed for export] *)
      zstep. if_cases GC1; zify_cond GC1; [exfalso; rewrite ?unsigned_lit in GC1 by lia; lia|].     (* [comment removed for export] *)
      zstep. zstep. if_cases GC2; zify_cond GC2; [exfalso; rewrite ?unsigned_lit in GC2 by lia; ubalign GC2; lia|].   (* [comment removed for export] *)
      zstep. zstep. if_cases K1; zify_cond K1; [exfalso; rewrite ?unsigned_lit in K1 by lia; lia|]. clear K1.   (* [comment removed for export] *)
      zstep.                                                     (* [comment removed for export] *)
      (* [comment removed for export] *)
      zstep. if_cases KE; zify_cond KE;
        [| zstep; zstep; zstep; zstep; zstep; if_cases GD; zify_cond GD; [exfalso; ubdec GD; lia|]].
      all: zstep; zstep; zstep.                                  (* [comment removed for export] *)
      all: replace (A' + n' + - A') with n' by lia.
      all: zstep.                                                (* [comment removed for export] *)
      all: apply evt_done.
      all: pose proof (RMalloc_ifaceP.RHEAP_blocks_nodup_proof _ _ _ HP2) as ND2.
      all: lazymatch goal with |- implM _ _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
      all: assert (HP3 : RHEAP sv ((p', A', n') :: LB) m3) by (eapply RHEAP_stack_frame; [exact HP2| exact MU2| exact WM2| repeat constructor; cbn; lia]).
      all: assert (AUX3 : rauxv_ok m3 AB) by (eapply rauxv_ok_stack_frame; [exact AUX2| exact MU2| exact WM2| repeat constructor; cbn; lia]).
      all: hide MU2; hide WM2.
      all: eapply implM_post_evt';
       [ eapply (proj1 (proj2 OD)) with (lo := lo) (B := AB) (A := A') (n := n') (p := p') (LB := (p', A', n') :: LB);
          try (apply eq_refl); rewrite ?unsigned_lit by lia;
          first [ exact HP3 | (left; reflexivity) | exact AUX3 | exact ST2 | exact MI2 | (rewrite errno_lit; exact ERR2) | (unfold RFREE_STACK; lia) | lia
                | (f_equal; lia) | match goal with |- ?G => idtac "LEFT:" G end ] | ].
      all: cbv beta; intros [] sd msd PO.
      all: destruct PO as (v0 & v1 & v2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m4 & -> & MI4 & ST4 & ERR4 & AUX4 & HPR4 & FAE4 & SOE4 & HP4).
      all: rewrite ?unsigned_lit in ST4 by lia; rewrite ?unsigned_lit in HPR4 by lia; rewrite errno_lit in ERR4; unfold RERRNO in ERR4.
      all: rewrite (RDriver_facts.lb_remove_hd p' (p', A', n') LB eq_refl ND2) in HPR4, HP4.
      all: ret_lit.
      all: trp HPR4; clear ST2 MI2 ERR2 AUX3 HP3.
      all: apply evt_done.
      (* [comment removed for export] *)
      all: pose proof (munch_refl [(lo, bv_unsigned sp)] m4) as MU5; pose proof (wmono_refl usegs m4) as WM5.
      all: zstep; do 10 zstep; zstep; zstep.
      all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
      all: assert (STF : stk usegs m5 lo (bv_unsigned sp)) by
       (release_frame FRL ST4 (bv_unsigned sp + -120); release_frame RC2 ST4 (bv_unsigned sp + -96); release_frame CC ST4 (bv_unsigned sp + -80);
        release_frame FRA ST4 (bv_unsigned sp); exact ST4).
      all: unhide MU; unhide WM; unhide MU2; unhide WM2.
      all: apply evt_done; unfold fuzz_oneU_post; do 14 eexists; exists F, fc, m5, errv2, LB.
      all: split; [reflexivity|]; split; [reflexivity|]; split; [exact MI4|]; split; [exact FZ|]; split; [exact STF|].
      all: split; [rewrite errno_lit; exact ERR4|].
      all: split; [eapply rauxv_ok_stack_frame; [exact AUX4| exact MU5| exact WM5| repeat constructor; cbn; lia]|].
      all: split;
      [ (* [comment removed for export] *)
        intros a Ha Hc Hw; destruct (HPRE a Ha Hc Hw) as [E0 W0];
        assert (HcL : rclient_addr LB (bv_unsigned sp + -192) a) by
         (destruct Hc as [Hc|[Hc|(bq & Hb & Hr)]]; [left; lia| right; left; exact Hc| right; right; exists bq; split; [exact (LBSUB bq Hb)| exact Hr]]);
        assert (OUTa : outside [(lo, bv_unsigned sp)] a) by
         (cbn; destruct Hc as [Hc|[Hc|(bq & Hb & Hr)]]; [lia| unfold ralloc_static in Hc; lia| pose proof (LBB bq (LBSUB bq Hb)); lia]);
        assert (E1 : m1 (wa a) = m (wa a)) by (apply MU; unfold wa; rewrite unsigned_lit by lia; exact OUTa);
        destruct (HPX a Ha HcL ltac:(cbn in OUTa; lia)) as [E2 W2];
        assert (E3 : m3 (wa a) = m2 (wa a)) by (apply MU2; unfold wa; rewrite unsigned_lit by lia; exact OUTa);
        destruct (HPR4 a Ha HcL) as [E4 W4];
        split; [congruence| intros Hv; apply W4, WM2, W2, WM, W0, Hv] | ].
      all: split; [eapply RHEAP_stack_frame; [exact HP4| exact MU5| exact WM5| repeat constructor; cbn; lia]|].
      all: split;
      [ split; [split; [exact CI1|]; split; [exact CI2|]; split; [exact CI3|]; split; [exact CI4| exact CI5]|];
        rewrite FAE4, FAE, FA; exists V; split; [exact PIN|]; unfold PVEC_GUARD, PVEC, PFALLBACK, patexit, patx_table, PCALL_THUNK, PAEF_GUARD, PDTOR_THUNK;
        split; [exact VV|]; split; [exact GU|]; split; [exact PV|]; split; [exact FB|]; split; [exact AT1|]; split; [exact AT2|]; split; [exact AT3|]; split; [exact AT4| exact AT5] | ].
      all: split; [congruence|].
      all: destruct (ps_fa s0') as [p0|]; [destruct FAREL as [-> E]; split; [reflexivity| congruence]|].
      all: destruct FAREL as (p1 & V1 & -> & E); exists p1, V1; split; [reflexivity| congruence].
    - (* [comment removed for export] *)
      destruct KL as (Nz & Uf & HP2 & RC2). unfold vec_cells in RC2.
      zstep. zstep. if_cases GB; zify_cond GB; [exfalso; rewrite ?unsigned_lit in GB by lia; lia|].   (* [comment removed for export] *)
      zstep.
      zstep. first [ lit_if | (if_cases K0; zify_cond K0; [clear K0| exfalso; lia]) ].
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.                                (* [comment removed for export] *)
      zstep.                                                     (* [comment removed for export] *)
      zstep. if_cases GC1; zify_cond GC1; [exfalso; rewrite ?unsigned_lit in GC1 by lia; lia|].     (* [comment removed for export] *)
      zstep. zstep. if_cases GC2; zify_cond GC2; [exfalso; rewrite ?unsigned_lit in GC2 by lia; ubalign GC2; lia|].   (* [comment removed for export] *)
      zstep. zstep. first [ lit_if | (if_cases K1; zify_cond K1; [clear K1| exfalso; lia]) ].
      zstep. ret_lit.                                            (* [comment removed for export] *)
      apply evt_done. cbn [HarnessM.odelete]. apply implM_ret. apply evt_done.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        pose proof (munch_refl [(lo, bv_unsigned sp)] mx) as MU5; pose proof (wmono_refl usegs mx) as WM5 end.
      zstep. do 10 zstep. zstep. zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
      assert (STF : stk usegs m5 lo (bv_unsigned sp)).
      { release_frame FRL ST2 (bv_unsigned sp + -120). release_frame RC2 ST2 (bv_unsigned sp + -96). release_frame CC ST2 (bv_unsigned sp + -80).
        release_frame FRA ST2 (bv_unsigned sp). exact ST2. }
      unhide MU. unhide WM. unhide MU2. unhide WM2.
      apply evt_done. unfold fuzz_oneU_post. do 14 eexists. exists F, fc, m5, errv2, LB.
      split; [reflexivity|]. split; [reflexivity|]. split; [exact MI2|]. split; [exact FZ|]. split; [exact STF|].
      split; [rewrite errno_lit; exact ERR2|].
      split; [eapply rauxv_ok_stack_frame; [| exact MU5| exact WM5| repeat constructor; cbn; lia]; eapply rauxv_ok_stack_frame; [exact AUX2| exact MU2| exact WM2| repeat constructor; cbn; lia]|].
      split.
      { intros a Ha Hc Hw. destruct (HPRE a Ha Hc Hw) as [E0 W0].
        assert (HcL : rclient_addr LB (bv_unsigned sp + -192) a).
        { destruct Hc as [Hc|[Hc|(bq & Hb & Hr)]]; [left; lia| right; left; exact Hc| right; right; exists bq; split; [exact (LBSUB bq Hb)| exact Hr]]. }
        assert (OUTa : outside [(lo, bv_unsigned sp)] a).
        { cbn. destruct Hc as [Hc|[Hc|(bq & Hb & Hr)]]; [lia| unfold ralloc_static in Hc; lia| pose proof (LBB bq (LBSUB bq Hb)); lia]. }
        assert (E1 : m1 (wa a) = m (wa a)) by (apply MU; unfold wa; rewrite unsigned_lit by lia; exact OUTa).
        destruct (HPX a Ha HcL ltac:(cbn in OUTa; lia)) as [E2 W2].
        assert (E3 : m5 (wa a) = m2 (wa a)) by (apply MU2; unfold wa; rewrite unsigned_lit by lia; exact OUTa).
        split; [congruence| intros Hv; apply WM2, W2, WM, W0, Hv]. }
      split; [eapply RHEAP_stack_frame; [| exact MU5| exact WM5| repeat constructor; cbn; lia]; eapply RHEAP_stack_frame; [exact HP2| exact MU2| exact WM2| repeat constructor; cbn; lia]|].
      split.
      { split; [split; [exact CI1|]; split; [exact CI2|]; split; [exact CI3|]; split; [exact CI4| exact CI5]|].
        rewrite FAE, FA. exists V. split; [exact PIN|]. unfold PVEC_GUARD, PVEC, PFALLBACK, patexit, patx_table, PCALL_THUNK, PAEF_GUARD, PDTOR_THUNK.
        split; [exact VV|]. split; [exact GU|]. split; [exact PV|]. split; [exact FB|]. split; [exact AT1|]. split; [exact AT2|]. split; [exact AT3|]. split; [exact AT4| exact AT5]. }
      split; [congruence|].
      destruct (ps_fa s0') as [p0|]; [destruct FAREL as [-> E]; split; [reflexivity| congruence]|].
      destruct FAREL as (p1 & V1 & -> & E). exists p1, V1. split; [reflexivity| congruence].
  Qed.

  (* [comment removed for export] *)
  Theorem fuzz_later : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem)
      (s : PState) (LB : list block) (D : Z) (payload : list Z) (AB lo : Z) (errv : word) (p : bptr),
    ps_fa s = Some p ->
    RHEAP s LB m ->
    bytes_at usegs m D (map (Z_to_bv 8) payload) -> Forall (fun c => 0 <= c < 256) payload ->
    rclient_range LB (bv_unsigned sp) D (zlength payload) ->
    0 < D -> D + zlength payload <= ATOP -> zlength payload < 2^26 ->
    client_static s LB m ->
    rauxv_ok m AB -> bv_unsigned sp <= AB ->
    stk usegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - PHARNESS_STACK ->
    rw_cells usegs m (errno_addr tp) [C4 errv] ->
    mem_inv usegs m -> frm0 fc ->
    tp = Z_to_bv 64 RATP -> bv_unsigned sp mod 16 = 0 ->
    a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 (zlength payload) ->
    ra = Z_to_bv 64 PTRUN_RET ->
    implM usegs (ProgP.fuzz_one payload) s
          (fuzz_oneU_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB AB lo m)
          (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 PFUZZ_ENTRY) fc None m (seg_rom usegs)).
  Proof.
    intros until p. intros FA HP DAT PLB DCR D0 DTOP NLT CS AUX SPB ST LOA LOS ERR MI FZ TP SPA A0 A1 RA.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof LOS as LOS'. unfold PHARNESS_STACK in LOS. atop_facts.
    destruct CS as [CI CST]. rewrite FA in CST. destruct CST as (V & PIN & VV & GU & PV & FB & PAT).
    destruct CI as (CI1 & CI2 & CI3 & CI4 & CI5). unfold UJT in CI5. unfold patexit, patx_table, PCALL_THUNK, PAEF_GUARD, PDTOR_THUNK in PAT. destruct PAT as (AT1 & AT2 & AT3 & AT4 & AT5).
    pose proof (RMalloc_ifaceP.RHEAP_block_range_proof s LB m) as LBR.
    assert (LBB : forall b, In b LB -> blk_addr b + blk_size b <= ATOP) by (intros b Hb; destruct (LBR b HP Hb) as (_ & _ & _ & R4 & _); exact R4).
    pose proof (LBR _ HP PIN) as (VB1 & VB2 & _ & VB4 & VB5). cbn [blk_addr blk_size fst snd] in VB1, VB2, VB4, VB5.
    clear LBR.
    set (n := zlength payload) in *.
    assert (N0 : 0 <= n) by (unfold n, zlength; lia).
    assert (BSL : Z.of_nat (length (map (Z_to_bv 8) payload)) = n) by (rewrite length_map; reflexivity).
    assert (DLO : D + n <= lo \/ bv_unsigned sp <= D).
    { destruct DCR as [H|[H|(b0 & Hb & Hr)]]; [right; exact H| left; lia| left; pose proof (LBB b0 Hb); lia]. }
    (* [comment removed for export] *)
    subst tp. rewrite errno_lit in ERR. unfold RERRNO in ERR.
    unfold guard1, PVEC_GUARD in GU. unfold PVEC in PV, AT5. unfold PFALLBACK in VV, FB.
    (* [comment removed for export] *)
    unfold ProgP.fuzz_one, HarnessM.fuzz_one, HarnessM.client_init.
    apply implM_bind_assoc. apply implM_get_l. cbv beta. rewrite FA. apply implM_retb.
    (* [comment removed for export] *)
    apply implM_from_evt.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    carve_frame 192%nat ST.
    subst a0 a1. unfold PFUZZ_ENTRY.
    do 11 zstep.
    do 4 zstep.
    zstep.                                                           (* [comment removed for export] *)
    zstep.                                                           (* [comment removed for export] *)
    zstep. first [ lit_if | (if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; cbn in K0; lia|]; clear K0) ].
    apply evt_done.
    lazymatch goal with |- implM _ _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    destruct (rw_cells_cut usegs m1 _ _ 1 FR) as [FRJ FRA]. clear FR. cbn [firstn skipn cells_size csize Nat.add] in FRJ, FRA.
    change (Z.of_nat 112) with 112 in FRA. replace (bv_unsigned sp + -192 + 112) with (bv_unsigned sp + -80) in FRA by lia.
    release_frame FRJ ST (bv_unsigned sp + -80).
    subst ra. unfold PTRUN_RET.
    eapply fuzz_join with (p := p) (V := V); rewrite ?unsigned_lit by lia;
      first [ exact HP | exact PIN | exact FA | exact DAT | exact PLB | exact DCR | exact D0 | exact DTOP | exact NLT | exact PV
            | exact ST | exact LOA | exact LOS' | exact FRA | (rewrite errno_lit; exact ERR) | exact MI | exact FZ | exact SPA
            | (unfold PFALLBACK; exact VV) | (unfold PFALLBACK; exact FB)
            | (unfold guard1, PVEC_GUARD; exact GU)
            | (unfold patexit, patx_table, PCALL_THUNK, PAEF_GUARD, PVEC, PDTOR_THUNK; split; [exact AT1|]; split; [exact AT2|]; split; [exact AT3|]; split; [exact AT4| exact AT5])
            | (split; [exact CI1|]; split; [exact CI2|]; split; [exact CI3|]; split; [exact CI4| exact CI5])
            | (eapply RHEAP_stack_frame; [exact HP| exact MU| exact WM| repeat constructor; cbn; lia])
            | (eapply rauxv_ok_stack_frame; [exact AUX| exact MU| exact WM| repeat constructor; cbn; lia])
            | (split; [| split; [reflexivity| split; [intros b Hb; exact Hb| rewrite FA; split; reflexivity]]];
               apply harness_pres_of_rheap_pres; eapply rheap_pres_of_munch; [exact MU| exact WM|];
               intros a Ha Hc; cbn; destruct Hc as [Hc|[Hc|(bq & Hb & Hr)]]; [lia| unfold ralloc_static in Hc; lia| pose proof (LBB bq Hb); lia])
            | reflexivity | lia
            | match goal with |- ?G => idtac "LEFT:" G end ].
  Qed.
End Proof.
End CANSEC1.
