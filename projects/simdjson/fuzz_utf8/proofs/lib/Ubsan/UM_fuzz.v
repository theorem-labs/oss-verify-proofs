(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: written for simdjson/fuzz_utf8's ubsan binary from simdjson/fuzz_minifyimpl's proofs/lib/Ubsan/UM_fuzz.v: the join walks this harness's code (its UBSan alignment and null checks, the inlined lambda's virtual call to validate_utf8, the pointer-overflow check, then the return) instead of minify's lambda and buffer delete, and the later call walks this harness's prologue and 112-byte frame. *)
(* fuzz_utf8's UBSan LLVMFuzzerTestOneInput: from its join point (both of its paths meet after the static vector's
   guard) to its return, and the later calls (the vector already built) from the entry. Each UBSan check on the
   way is shown not to fire. *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import Stdio_pure.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Ubsan Require Import UImg.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Ubsan Require Import RMallocRep RMallocTree RMalloc_iface ROpNew_iface.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Ubsan Require RMalloc_ifaceP.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Spec Require Import Prelim Monad Stdio Malloc PState HarnessU ProgP.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Ubsan Require Import PAtexit_cells RunDraw PU_iface PM_kit PM_iface UM_guards.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation mem := (word -> option byte).

Section CANSEC1. Context {rc : runConstT}.

Lemma implM_get_l : forall {B} (k : PState -> Monad.M PState B) s Q ms,
  implM usegs (k s) s Q ms -> implM usegs (mbind mget k) s Q ms.
Proof. intros. exact H. Qed.

Section Proof.
  Hypothesis VU : vutf8_stmt.

  (* The join: [ld s5,0x28(s4)] and its alignment check, [ld s3,0x30(s4)] and its alignment check, the null check
     of s5, [ld a0,0(s5)] and its null and alignment checks, [ld a1,0(a0); ld a3,0x28(a1); mv a1,s1; mv a2,s0;
     jalr a3] calls validate_utf8, then the pointer-overflow check of s5 + 8, [addi s5,s5,8; beq s3,s5] leaves the
     comparison loop at once, [mv a0,zero], restores ra and s0..s9 and returns 0. *)
  Theorem fuzz_join_proof : fuzz_join_stmt.
  Proof.
    unfold fuzz_join_stmt.
    intros until V. intros HP PIN FA JR DAT PLB DCR D0 DTOP NLT CI VV GU PV FB PAT AUX SPB ST LOA LOS FRA ERR MI FZ TP SPA.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    unfold PHARNESS_STACK in LOS. atop_facts.
    subst tp. rewrite errno_lit in ERR. unfold RERRNO in ERR.
    set (n := zlength pl) in *.
    assert (N0 : 0 <= n) by (unfold n, zlength; lia).
    destruct JR as (HPRE & SOE0 & LBSUB & FAREL).
    destruct CI as (CI1 & CI2).
    unfold guard1, PVEC_GUARD in GU. unfold PVEC in PV, PAT. unfold PFALLBACK in FB, VV. unfold PFALLBACK_VT in FB.
    unfold patexit, patx_table, PCALL_THUNK, PAEF_GUARD, PDTOR_THUNK in PAT. destruct PAT as (AT1 & AT2 & AT3 & AT4 & AT5).
    pose proof (RMalloc_ifaceP.RHEAP_block_range_proof s LB m) as LBR.
    assert (LBB : forall b, In b LB -> blk_addr b + blk_size b <= ATOP) by (intros b Hb; destruct (LBR b HP Hb) as (_ & _ & _ & R4 & _); exact R4).
    pose proof (LBR _ HP PIN) as (VB1 & VB2 & _ & VB4 & VB5). cbn [blk_addr blk_size fst snd] in VB1, VB2, VB4, VB5.
    clear LBR.
    assert (DLO : D + n <= lo \/ bv_unsigned sp <= D).
    { destruct DCR as [H|[H|(b0 & Hb & Hr)]]; [right; exact H| left; lia| left; pose proof (LBB b0 (LBSUB b0 Hb)); lia]. }
    apply implM_ret.
    destruct (stk_split usegs m lo (bv_unsigned sp + -112) (bv_unsigned sp + -88) ST ltac:(lia)) as [STL STJ].
    unfold PJOIN, PSTATICS.
    zstep.                                                       (* ld s5: the vector's begin *)
    zstep. zstep. if_cases GA1; zify_cond GA1; [exfalso; ubalign GA1; lia|].     (* its alignment *)
    zstep.                                                       (* ld s3: the vector's end *)
    zstep. zstep. if_cases GA2; zify_cond GA2; [exfalso; ubalign GA2; lia|].     (* its alignment *)
    zstep. if_cases GA3; zify_cond GA3; [exfalso; lia|].         (* s5 not null *)
    zstep.                                                       (* ld a0: the implementation *)
    zstep. first [ lit_if | (if_cases GA4; zify_cond GA4; [exfalso; lia|]) ].                  (* not null *)
    zstep. zstep. first [ lit_if | (if_cases GA5; zify_cond GA5; [exfalso; ubalign GA5; lia|]) ].  (* aligned *)
    zstep. zstep.                                                (* its vtable, validate_utf8 *)
    zstep. zstep.                                                (* Data, Size *)
    zstep.                                                       (* jalr *)
    eapply evt_cut.
    { eapply VU with (D := D) (pl := pl) (lo := lo); try (apply eq_refl); change (zlength pl) with n; rewrite ?unsigned_lit by lia;
        first [ exact DAT | exact PLB | exact STL | exact MI | (unfold VUTF8_STACK; lia) | lia ]. }
    intros ms4 PO.
    destruct PO as (y0 & y1 & y2 & r0 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & m4 & -> & RV & MU4 & WM4 & MI4 & ST4).
    rewrite ?unsigned_lit in MU4, ST4 by lia. unfold VUTF8_STACK in MU4.
    ret_lit.
    assert (STJ4 : stk usegs m4 (bv_unsigned sp + -112) (bv_unsigned sp + -88))
      by (eapply stk_transport_disjoint; [exact STJ| exact MU4| exact WM4| cbn; lia]).
    assert (HP4 : RHEAP s LB m4) by (eapply RHEAP_stack_frame; [exact HP| exact MU4| exact WM4| repeat constructor; cbn; lia]).
    assert (AUX4 : rauxv_ok m4 AB) by (eapply rauxv_ok_stack_frame; [exact AUX| exact MU4| exact WM4| repeat constructor; cbn; lia]).
    assert (HPR4 : harness_pres LB0 (bv_unsigned sp) m0 m4).
    { intros a Ha Hc Hw. destruct (HPRE a Ha Hc Hw) as [E0 W0].
      assert (OUTa : outside [(bv_unsigned sp + -112 - 96, bv_unsigned sp + -112)] a).
      { cbn. destruct Hc as [Hc|[Hc|(bq & Hb & Hr)]]; [lia| unfold ralloc_static in Hc; lia| pose proof (LBB bq (LBSUB bq Hb)); lia]. }
      assert (E1 : m4 (wa a) = m (wa a)) by (apply MU4; unfold wa; rewrite unsigned_lit by lia; exact OUTa).
      split; [congruence| intros Hv; apply WM4, W0, Hv]. }
    trm MU4 WM4.
    (* the client statics, each cell carried over the call by trm *)
    assert (CS4 : client_static s LB m4).
    { unfold client_static. split; [split; [exact CI1| exact CI2]|]. rewrite FA. exists V. split; [exact PIN|].
      unfold PVEC_GUARD, PVEC, PFALLBACK, PFALLBACK_VT, patexit, patx_table, PCALL_THUNK, PAEF_GUARD, PDTOR_THUNK, guard1.
      split; [exact VV|]. split; [exact GU|]. split; [exact PV|]. split; [exact FB|].
      split; [exact AT1|]. split; [exact AT2|]. split; [exact AT3|]. split; [exact AT4| exact AT5]. }
    clear STL STJ ST HP AUX DAT.
    (* back in the harness *)
    zstep. zstep. if_cases GB; zify_cond GB; [exfalso; rewrite ?unsigned_lit in GB by lia; lia|].   (* s5 + 8 does not wrap *)
    zstep.                                                       (* addi s5, s5, 8 *)
    zstep. first [ lit_if | (if_cases K1; zify_cond K1; [clear K1| exfalso; lia]) ].   (* the loop is empty *)
    zstep.                                                       (* mv a0, zero *)
    do 11 zstep.                                                 (* ra, s0..s9 *)
    zstep. zstep.                                                (* addi sp; ret *)
    assert (STF : stk usegs m4 lo (bv_unsigned sp)).
    { assert (S1 : stk usegs m4 lo (bv_unsigned sp + -88)) by (eapply stk_merge; [exact ST4| exact STJ4| lia]).
      release_frame FRA S1 (bv_unsigned sp). exact S1. }
    apply evt_done. unfold fuzz_oneU_post. do 14 eexists. exists F, fc, m4, errv, LB.
    split; [reflexivity|]. split; [reflexivity|]. split; [exact MI4|]. split; [exact FZ|]. split; [exact STF|].
    split; [rewrite errno_lit; exact ERR|].
    split; [exact AUX4|]. split; [exact HPR4|]. split; [exact HP4|]. split; [exact CS4|].
    split; [congruence|].
    destruct (ps_fa s0') as [p0|]; [destruct FAREL as [-> E]; split; [reflexivity| congruence]|].
    destruct FAREL as (p1 & V1 & -> & E). exists p1, V1. split; [reflexivity| congruence].
  Qed.

  (* A later call: the prologue [addi sp,-112; sd ra,s0..s9; mv s0,a1; mv s1,a0; auipc; addi s4; lb a0,8(s4);
     fence; beqz a0] finds the guard set and reaches the join. *)
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
    destruct CI as (CI1 & CI2). unfold patexit, patx_table, PCALL_THUNK, PAEF_GUARD, PDTOR_THUNK in PAT. destruct PAT as (AT1 & AT2 & AT3 & AT4 & AT5).
    pose proof (RMalloc_ifaceP.RHEAP_block_range_proof s LB m) as LBR.
    assert (LBB : forall b, In b LB -> blk_addr b + blk_size b <= ATOP) by (intros b Hb; destruct (LBR b HP Hb) as (_ & _ & _ & R4 & _); exact R4).
    pose proof (LBR _ HP PIN) as (VB1 & VB2 & _ & VB4 & VB5). cbn [blk_addr blk_size fst snd] in VB1, VB2, VB4, VB5.
    clear LBR.
    set (n := zlength payload) in *.
    assert (N0 : 0 <= n) by (unfold n, zlength; lia).
    assert (BSL : Z.of_nat (length (map (Z_to_bv 8) payload)) = n) by (rewrite length_map; reflexivity).
    (* the payload lies below the stack or above sp: so the frame's stores keep DAT *)
    assert (DLO : D + n <= lo \/ bv_unsigned sp <= D).
    { destruct DCR as [H|[H|(b0 & Hb & Hr)]]; [right; exact H| left; lia| left; pose proof (LBB b0 Hb); lia]. }
    subst tp. rewrite errno_lit in ERR. unfold RERRNO in ERR.
    unfold guard1, PVEC_GUARD in GU. unfold PVEC in PV, AT5. unfold PFALLBACK in VV, FB.
    unfold ProgP.fuzz_one, HarnessU.fuzz_one, HarnessU.client_init.
    apply implM_bind_assoc. apply implM_get_l. cbv beta. rewrite FA. apply implM_retb.
    apply implM_from_evt.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    carve_frame 112%nat ST.
    subst a0 a1. unfold PFUZZ_ENTRY.
    do 12 zstep.                                                 (* addi sp; sd ra, s0..s9 *)
    do 4 zstep.                                                  (* mv s0; mv s1; auipc; addi s4 *)
    zstep.                                                       (* lb a0, 8(s4): the guard *)
    zstep.                                                       (* fence *)
    zstep. first [ lit_if | (if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; cbn in K0; lia|]; clear K0) ].
    apply evt_done.
    lazymatch goal with |- implM _ _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    destruct (rw_cells_cut usegs m1 _ _ 1 FR) as [FRJ FRA]. clear FR. cbn [firstn skipn cells_size csize Nat.add] in FRJ, FRA.
    change (Z.of_nat 24) with 24 in FRA. replace (bv_unsigned sp + -112 + 24) with (bv_unsigned sp + -88) in FRA by lia.
    release_frame FRJ ST (bv_unsigned sp + -88).
    subst ra. unfold PTRUN_RET.
    eapply fuzz_join_proof with (p := p) (V := V); rewrite ?unsigned_lit by lia;
      first [ exact HP | exact PIN | exact FA | exact DAT | exact PLB | exact DCR | exact D0 | exact DTOP | exact NLT | exact PV
            | exact ST | exact LOA | exact LOS' | exact FRA | (rewrite errno_lit; exact ERR) | exact MI | exact FZ | exact SPA
            | (unfold PFALLBACK; exact VV) | (unfold PFALLBACK, PFALLBACK_VT; exact FB)
            | (unfold guard1, PVEC_GUARD; exact GU) | (unfold PVEC; exact PV)
            | (unfold patexit, patx_table, PCALL_THUNK, PAEF_GUARD, PVEC, PDTOR_THUNK; split; [exact AT1|]; split; [exact AT2|]; split; [exact AT3|]; split; [exact AT4| exact AT5])
            | (split; [exact CI1| exact CI2])
            | (eapply RHEAP_stack_frame; [exact HP| exact MU| exact WM| repeat constructor; cbn; lia])
            | (eapply rauxv_ok_stack_frame; [exact AUX| exact MU| exact WM| repeat constructor; cbn; lia])
            | (split; [| split; [reflexivity| split; [intros b Hb; exact Hb| rewrite FA; split; reflexivity]]];
               apply harness_pres_of_rheap_pres; eapply rheap_pres_of_munch; [exact MU| exact WM|];
               intros a Ha Hc; cbn; destruct Hc as [Hc|[Hc|(bq & Hb & Hr)]]; [lia| unfold ralloc_static in Hc; lia| pose proof (LBB bq Hb); lia])
            | reflexivity | lia ].
  Qed.
End Proof.
End CANSEC1.
