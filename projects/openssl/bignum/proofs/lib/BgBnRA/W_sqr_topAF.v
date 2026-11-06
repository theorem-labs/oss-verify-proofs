(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac ZBridge RzCPS. 
From OSSVerify.Proofs.openssl.bignum.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Malloc Prog BnBase BnWords BnWordsCorrect BnModel BnTree BnInv BnSpecs BnMInv BgState BgInv BgLib BgWords BgArith.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgA Require Import Layout R_unwind_chain RT_iface RT_client_kit D_defs I_lkit.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnMem BnTacX BnArith.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr.
From OSSVerify.Proofs.openssl.bignum.lib.BnAsan Require Import AsKit AsLoop AsLeaf.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnAsan Require Import LibKitA ARun BnHeapA ImplA ImplAX UnwindA EdgesA AsStruct RtCallA W_cryptoA W_smallA W_topA AsStruct2.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnAsan Require BnRepDefs BnRepA BnIfaceA.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepA Require Import BgRepDefs BgRep BgLayer BgIface.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRA Require Import BnAKitAF BnCallAF W_callsAF W_div_tailAF W_bndivAF ExpKitAF AFrameKit AFrameEnv.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepA Require Import BgLayerF BgIfaceF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition BN_SQR : Z := 0x23002c.
Definition BN_SQR_FIXED_TOP : Z := 0x230074.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).
Local Notation E_sqr_ft := (E_BN_sqr_22fe64 : uk_call BN_SQR 0x23004c BN_SQR_FIXED_TOP).

Variables (CSF CMF : Z).
Hypothesis CSF16 : 16 <= CSF.
Hypothesis CMF0 : 0 <= CMF.
Definition BN_SQR_TOP_STACK : Z := 32 + CSF.

Hypothesis bn_sqr_fixed_top_walkA : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
    (lo : Z) (ras : list Z) (rr rx : bnref) (ar ax ac : Z) (qc : bptr),
  bn_preA Σ ls m OW LB PL EA sp lo CSF CMF ->
  fr_room 1 ls OW LB ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx BN_SQR_FIXED_TOP (bv_unsigned ra :: ras) ->
  tp = wz TP_A -> ref_at ls OW PL rr ar -> ref_at ls OW PL rx ax -> hpl PL rr -> rx <> ROne -> nbuf PL rx -> pl_ctx PL = Some (ac, qc) ->
  a0 = wz ar -> a1 = wz ax -> a2 = wz ac ->
  implA (bn_sqr_fixed_top (tree_ops bptr) rr rx ls) Σ
    (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA CMF (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz BN_SQR_FIXED_TOP) fc None m (seg_rom bgasegs)).

Lemma BN_sqr_walkA : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
    (lo : Z) (ras : list Z) (rr rx : bnref) (ar ax ac : Z) (qc : bptr),
  bn_preA Σ ls m OW LB PL EA sp lo BN_SQR_TOP_STACK CMF ->
  fr_room 1 ls OW LB ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx BN_SQR (bv_unsigned ra :: ras) ->
  tp = wz TP_A -> ref_at ls OW PL rr ar -> ref_at ls OW PL rx ax ->
  hpl PL rr -> rx <> ROne -> nbuf PL rx -> pl_ctx PL = Some (ac, qc) ->
  a0 = wz ar -> a1 = wz ax -> a2 = wz ac ->
  implA (BN_sqr (tree_ops bptr) rr rx ls) Σ
    (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA CMF (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz BN_SQR) fc None m (seg_rom bgasegs)).
Proof.
  intros until qc. intros PRE ROOM UW CTX -> HR HX HPr NROx NBx EC -> -> ->.
  pose proof PRE as (HEAP & LS & FROK & ST & CEIL & LO & SPT & SP16 & MI & CNT & CRED & FAL & NOFR).
  pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
  pose proof LO as LO'. unfold BN_SQR_TOP_STACK in LO. pose proof CSF16 as CSFP.
  unfold BN_SQR, MallocRep.wz.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3, SPT.
  unfold BN_sqr.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgasegs m) as WM.
  apply implA_from_evt.
  assert (LO32 : lo <= bv_unsigned sp - 32) by (clear - LO CSFP; lia).
  carve_frame 32%nat ST. do 6 step. zstep. step.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  assert (HWL : Forall (w_lib ls OW PL lo (bv_unsigned sp)) [(bv_unsigned sp - 32, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
  assert (WOK : Forall (w_ok OW LB ls PL EA (bv_unsigned sp) []) [(bv_unsigned sp - 32, bv_unsigned sp)]) by (constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia| constructor]).
  pose proof (lib_state_frame Σ LB (bv_unsigned sp) USTACK_TOP [] ls m m1 OW PL EA _ HEAP LS MU WM FROK WOK) as LS1.
  match goal with FRx : rw_cells _ m1 (bv_unsigned sp + -32) ?fr, STx : stk _ m1 _ _, MIx : mem_inv _ m1 |- _ =>
    let pre := drop2 fr in
    assert (ENV : cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -32) s0 ra (Some ras) CMF Σ ls OW m pre 0 Σ ls m1 OW);
    [ unfold cenvA; split;
      [ unfold cenv_ok; split; [exact CEIL|]; split; [clear - LO CSFP; lia|]; split; [clear; lia|]; split; [unfold USTACK_TOP; clear - SPT; lia|]; split; [exact SP16|];
        split; [clear - SP16; Z.div_mod_to_equations; lia|]; split; [exact CNT|]; split; [exact CRED|]; split; [exact FROK|]; split; [exact FAL| exact NOFR] |];
      split; [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL ltac:(unfold USTACK_TOP; clear - SPT; lia))|];
      split; [exact STx|]; split; [exact MIx|];
      split; [exact (seg_ax_pres' _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU HWL CEIL ltac:(clear - LO CSFP; lia))|];
      split; [lia|]; split; [apply cnt_eq_refl|]; split; [apply refs_stable_refl|];
      split; [cbn [app]; exact FRx|]; split; [cbn; lia|]; unfold uw_opt;
      eapply uw_chain_munch_nw; [exact UW | exact MU |]; constructor; [cbn; lia | constructor]
    | ] end.
  pose proof ENV as (OK & HEAP1 & _).
  apply evt_done. unfold bbind at 1. cbn [bind tree_ops].
  eapply implA_bind.
  { eapply (bn_sqr_fixed_top_walkA) with (lo := lo) (ras := bv_unsigned ra :: ras) (OW := OW) (LB := LB) (PL := PL) (EA := EA)
             (rr := rr) (rx := rx) (ar := ar) (ax := ax) (ac := ac) (qc := qc);
      [| | | | reflexivity | exact HR | exact HX | exact HPr | exact NROx | exact NBx | exact EC | reflexivity | reflexivity | reflexivity].
    - eapply cenv_preA; [exact ENV | exact LS1 | clear - LO CSFP; lia | lia].
    - eapply cenv_roomA; [exact ENV | exact ROOM | clear; lia].
    - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl ENV).
    - rewrite unsigned_lit by lia. exact (uk_ctx_call _ _ _ _ E_sqr_ft CTX). }
  cbv beta. intros [u1 ls1] Σ1 ms1 PO.
  apply (bn_postA_cpost LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -32) CMF Σ ls OW) in PO; [| exact OK | exact HEAP1].
  cbn [fst snd] in *.
  destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F1 & fc1 & m3 & OW1 & PLz1 & -> & CP1 & (EPLz1 & ->)).
  subst PLz1. specialize (CP1 eq_refl).
  lazymatch type of ENV with cenvA _ _ _ _ _ _ _ _ _ _ _ _ _ ?pre _ _ _ _ _ =>
    assert (E1 : cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -32) s0 ra (Some ras) CMF Σ ls OW m pre (0 + CMF) Σ1 ls1 m3 OW1 /\ lib_state ls1 m3 OW1 PL EA)
      by (eapply cenv_postA; [exact ENV | exact CP1]) end.
  destruct E1 as (ENV1 & LS1').
  pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP1) as RS1.
  fix_ret. unfold MallocRep.wz.
  clear CP1.

  pose proof (ref_at_stable _ _ _ _ _ _ _ RS1 HR) as HR1.
  unfold bbind, bget, bset. cbn [bind ret tree_ops tbind fst snd]. apply implA_ret_evt.
  unfold MallocRep.wz.
  zstep. zstep. step.
  eapply (ctop_callA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -32) s0 ra (Some ras) CMF Σ ls OW m ltac:(clear - LO CSFP; lia) _ _ _ Σ1 ls1 m3 OW1 rr ar);
    [exact ENV1 | exact LS1' | exact HR1 | exact (hpl_wref PL rr HPr) |].
  intros m4 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 ls4 ENV2 LS2.
  fix_ret.

  pose proof (cenv_finalA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -32) s0 ra (Some ras) CMF Σ ls OW m _ _ _ _ _ _ ENV2 LS2 ltac:(lia))
    as (F1' & F2 & F3 & F4 & F5 & F6 & F7).
  env_openA ENV2.
  zstep. do 4 step.
  release_frame FRe STe (bv_unsigned sp). step. step.
  apply evt_done. unfold bn_postA. do 17 eexists. exists m4, OW1, PL. split; [reflexivity|]. cbn [fst snd].
  split; [exact F1'|]. split; [exact F2|]. split; [exact STe|]. split; [exact F3|]. split; [exact F4|]. split; [exact F5|].
  split; [exact F6|]. split; [exact F7|]. split; reflexivity.
Qed.
End WithRT.
