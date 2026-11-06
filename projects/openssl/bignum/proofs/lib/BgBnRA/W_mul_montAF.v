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
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Malloc Prog BnBase BnWords BnWordsCorrect BnModel BnTree BnInv BnSpecs BnMInv BgState BgInv BgLib.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgA Require Import Layout R_unwind_chain RT_iface RT_client_kit D_defs I_lkit.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnMem BnTacX.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr ShiftPure.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnP Require Import BnLeaves.
From OSSVerify.Proofs.openssl.bignum.lib.BnAsan Require Import AsKit AsLoop.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnAsan Require Import LibKitA ARun BnHeapA ImplA ImplAX UnwindA EdgesA AsStruct RtCallA W_cryptoA W_smallA AsStruct2.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnAsan Require BnRepDefs BnRepA BnIfaceA.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepA Require Import BgRepDefs BgRep BgLayer BgIface.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BgWords BgArith BgMont.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnAsan Require Import W_ctxA W_ctx_getA W_ctx_endA.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRA Require Import BnAKitAF BnCallAF W_expandAF W_callsAF W_ctxAF W_ctx_getAF W_ctx_endAF ExpKitAF AFrameKit AFrameEnv.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepA Require Import BgLayerF BgIfaceF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition BN_MUL_MONT_FIXED_TOP : Z := 0x227550.
Definition BN_SQR_FIXED_TOP : Z := 0x230074.
Definition BN_MUL_FIXED_TOP : Z := 0x22a928.
Definition BN_FROM_MONTGOMERY_WORD : Z := 0x2276b8.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Section Proofs.

  Variables (CS CM CFW : Z).
  Hypothesis CSstart : BN_CTX_START_STACK <= CS.
  Hypothesis CSget : BN_CTX_GET_STACK <= CS.
  Hypothesis CSend : BN_CTX_END_STACK <= CS.
  Hypothesis CM0 : 0 <= CM.
  Hypothesis CFW0 : 0 <= CFW.
  Definition MMFT_STACK : Z := 64 + CS.
  Definition MMFT_COST : Z := 2 * MC + CM + CFW.

  Ltac strip2 l := lazymatch l with
    | cons _ (cons _ nil) => constr:(@nil cell)
    | cons ?x ?t => let r := strip2 t in constr:(cons x r)
    end.

  Hypothesis bn_sqr_fixed_top_walkA : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
      (lo : Z) (ras : list Z) (rr rx : bnref) (ar ax ac : Z) (qc : bptr),
    bn_preA Σ ls m OW LB PL EA sp lo CS CM ->
    fr_room 1 ls OW LB ->
    uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx BN_SQR_FIXED_TOP (bv_unsigned ra :: ras) ->
    tp = wz TP_A -> ref_at ls OW PL rr ar -> ref_at ls OW PL rx ax -> hpl PL rr -> rx <> ROne -> nbuf PL rx -> pl_ctx PL = Some (ac, qc) ->
    a0 = wz ar -> a1 = wz ax -> a2 = wz ac ->
    implA (bn_sqr_fixed_top (tree_ops bptr) rr rx ls) Σ
      (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA CM (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_SQR_FIXED_TOP) fc None m (seg_rom bgasegs)).

  Hypothesis bn_mul_fixed_top_walkA : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
      (lo : Z) (ras : list Z) (rr rx ry : bnref) (ar ax ay ac : Z) (qc : bptr),
    bn_preA Σ ls m OW LB PL EA sp lo CS CM ->
    uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx BN_MUL_FIXED_TOP (bv_unsigned ra :: ras) ->
    tp = wz TP_A -> ref_at ls OW PL rr ar -> ref_at ls OW PL rx ax -> ref_at ls OW PL ry ay -> hpl PL rr -> ry <> ROne -> nbuf PL rx -> nbuf PL ry -> pl_ctx PL = Some (ac, qc) ->
    a0 = wz ar -> a1 = wz ax -> a2 = wz ay -> a3 = wz ac ->
    implA (bn_mul_fixed_top (tree_ops bptr) rr rx ry ls) Σ
      (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA CM (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_MUL_FIXED_TOP) fc None m (seg_rom bgasegs)).

  Hypothesis bn_from_montgomery_word_walkA : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
      (lo : Z) (ras : list Z) (rt rx : bnref) (at_ ax am : Z) (qm : bptr),
    bn_preA Σ ls m OW LB PL EA sp lo CS CFW ->
    uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx BN_FROM_MONTGOMERY_WORD (bv_unsigned ra :: ras) ->
    tp = wz TP_A -> ref_at ls OW PL rt at_ -> ref_at ls OW PL rx ax -> wref PL rt -> wref PL rx -> pl_mont PL = Some (am, qm) ->
    a0 = wz at_ -> a1 = wz ax -> a2 = wz am ->
    implA (bn_from_montgomery_word (tree_ops bptr) rt rx ls) Σ
      (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA CFW (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_FROM_MONTGOMERY_WORD) fc None m (seg_rom bgasegs)).

  Lemma bn_mul_mont_fixed_top_walkA : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
      (lo : Z) (ras : list Z) (rr ra_ rb : bnref) (ar aa ab am ac : Z) (qm qc : bptr),
    bn_preA Σ ls m OW LB PL EA sp lo MMFT_STACK MMFT_COST ->
    fr_room 1 ls OW LB ->
    uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx BN_MUL_MONT_FIXED_TOP (bv_unsigned ra :: ras) ->
    tp = wz TP_A -> ref_at ls OW PL rr ar -> ref_at ls OW PL ra_ aa -> ref_at ls OW PL rb ab -> wref PL rr -> rb <> ROne -> nbuf PL ra_ -> nbuf PL rb ->
    pl_mont PL = Some (am, qm) -> pl_ctx PL = Some (ac, qc) ->
    a0 = wz ar -> a1 = wz aa -> a2 = wz ab -> a3 = wz am -> a4 = wz ac ->
    implA (bn_mul_mont_fixed_top (tree_ops bptr) rr ra_ rb ls) Σ
      (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA MMFT_COST (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_MUL_MONT_FIXED_TOP) fc None m (seg_rom bgasegs)).
  Proof.
    intros until qc. intros PRE ROOM UW CTX -> HAr HAa HAb WRr NROb NBa NBb HPM HPC -> -> -> -> ->.
    pose proof PRE as (HEAP & LS & FROK & ST & CEIL & LO & SPT & SP16 & MI & CNT & CRED & FAL & NOFR).
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
    pose proof LO as LO'. unfold MMFT_STACK in LO'.
    pose proof MC0 as MCP.
    unfold BN_MUL_MONT_FIXED_TOP, MallocRep.wz.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
    assert (CS16 : 16 <= CS) by (pose proof CSend as H; unfold BN_CTX_END_STACK in H; clear - H; lia).
    pose proof (AH_nodup_l _ _ _ _ HEAP) as ND.
    pose proof (ref_at_montN ls OW PL am qm HPM) as HAn.

    destruct (ref_sh_any _ _ _ _ _ _ _ _ _ _ HEAP LS FROK NOFR HAa) as (ACCa & ALa & Aa0 & AaC).
    destruct (ref_sh_any _ _ _ _ _ _ _ _ _ _ HEAP LS FROK NOFR HAb) as (ACCb & ALb & Ab0 & AbC).
    destruct (ref_sh_any _ _ _ _ _ _ _ _ _ _ HEAP LS FROK NOFR HAn) as (ACCn & ALn & An0 & AnC).
    assert (AaR : 0 < aa < 2^64) by (clear - Aa0 AaC CEIL LO' SPR CS16; lia).
    assert (AbR : 0 < ab < 2^64) by (clear - Ab0 AbC CEIL LO' SPR CS16; lia).
    destruct (AH_shb _ _ _ _ HEAP) as (SHB1 & SHB2).
    assert (OFF : offshW [(bv_unsigned sp - 64, bv_unsigned sp)]) by (cbn [offshW]; unfold SHLO, SHHI, BnHeapA.ACEIL in *; clear - C1 C2 C3 CEIL LO' SPR CS16; lia).
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgasegs m) as WM.
    unfold bn_mul_mont_fixed_top, bbind, bget, bret, bunr. cbn [bind ret unreachable tree_ops tbind fst snd].
    apply implA_from_evt.
    set (bn := getbn RMontN ls). set (ba := getbn ra_ ls). set (bb := getbn rb ls).
    pose proof (top_small _ _ _ _ _ _ _ LS HAn) as Tn. pose proof (top_small _ _ _ _ _ _ _ LS HAa) as Ta. pose proof (top_small _ _ _ _ _ _ _ LS HAb) as Tb.
    fold bn in Tn. fold ba in Ta. fold bb in Tb.

    carve_frame 64%nat ST. do 9 step. do 5 step. do 3 step.

    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mQ end.
    assert (HWLq : Forall (w_lib ls OW PL lo (bv_unsigned sp)) [(bv_unsigned sp + -64, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
    assert (WOKq : Forall (w_ok OW LB ls PL EA (bv_unsigned sp) []) [(bv_unsigned sp + -64, bv_unsigned sp)]).
    { constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia| constructor]. }
    pose proof (lib_state_frame Σ LB (bv_unsigned sp) USTACK_TOP [] ls m mQ OW PL EA _ HEAP LS MU WM FROK WOKq) as LSq.
    pose proof (const_one_cells_of_heap _ _ _ _ (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWLq CEIL ltac:(unfold USTACK_TOP; lia))) as ONEq.
    destruct (lib_state_open_ro [] ls mQ OW PL EA ra_ aa LSq ND HAa ltac:(intros []) ONEq) as ((Da & BNa & _) & _ & _ & _).
    destruct (lib_state_open_ro [] ls mQ OW PL EA rb ab LSq ND HAb ltac:(intros []) ONEq) as ((Db & BNb & _) & _ & _ & _).
    destruct (lib_state_open_ro [] ls mQ OW PL EA RMontN (am + 24) LSq ND HAn ltac:(intros []) ONEq) as ((Dn & BNn & _) & _ & _ & _).
    fold ba in BNa. fold bb in BNb. fold bn in BNn. unfold bn_cells in BNa, BNb, BNn.
    clear HWLq WOKq LSq ONEq.

    do 3 step. shl_with ACCn ALn. step. chk0.

    do 3 step. shl_with ACCa ALa.
    step. unfold MallocRep.wz at 1. rewrite (sx32_small (Z.of_nat (bn_top bn))) by (clear - Tn; lia).
    chk0.

    do 3 step. shl_with ACCb ALb.
    step. unfold MallocRep.wz at 1. rewrite (sx32_small (Z.of_nat (bn_top ba))) by (clear - Ta; lia).
    chk0.
    step. unfold MallocRep.wz at 1. rewrite (sx32_small (Z.of_nat (bn_top bb))) by (clear - Tb; lia).

    step. rewrite !unsigned_lit by (clear - Ta Tb; lia). rewrite (bn_swrap32_small _) by (clear - Ta Tb; lia).
    step. rewrite unsigned_lit by (clear - Tn; lia). rewrite Z.shiftl_mul_pow2, Z.pow_1_r by lia. rewrite (bn_swrap32_small _) by (clear - Tn; lia).
    step. rewrite lts_small by (clear - Ta Tb Tn; lia).
    destruct (Z.ltb_spec (Z.of_nat (bn_top bn) * 2) (Z.of_nat (bn_top bb) + Z.of_nat (bn_top ba))) as [LT|GE]; cbn [negb].
    { replace (2 * bn_top bn <? bn_top ba + bn_top bb)%nat with true by (symmetry; apply Nat.ltb_lt; clear - LT; lia).
      apply evt_done. apply implA_unr. }
    replace (2 * bn_top bn <? bn_top ba + bn_top bb)%nat with false by (symmetry; apply Nat.ltb_ge; clear - GE; lia).
    clear BNa BNb BNn Da Db Dn ACCa ACCb ACCn OFF.
    step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mP end.
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; lia).
    assert (HWL : Forall (w_lib ls OW PL lo (bv_unsigned sp)) [(bv_unsigned sp + -64, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
    assert (WOK : Forall (w_ok OW LB ls PL EA (bv_unsigned sp) []) [(bv_unsigned sp + -64, bv_unsigned sp)]).
    { constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia| constructor]. }
    pose proof (lib_state_frame Σ LB (bv_unsigned sp) USTACK_TOP [] ls m mP OW PL EA _ HEAP LS MU WM FROK WOK) as LS0.
    lazymatch type of FR with rw_cells _ _ _ ?fr => let p := strip2 fr in
      assert (EV0 : cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -64) s0 ra (Some ras) MMFT_COST Σ ls OW m p 0 Σ ls mP OW) end.
    { unfold cenvA, cenv_ok.
      split; [split; [exact CEIL|]; split; [lia|]; split; [lia|]; split; [unfold USTACK_TOP; lia|]; split; [exact SP16|];
              split; [clear - SP16; Z.div_mod_to_equations; lia|]; split; [exact CNT|]; split; [exact CRED|]; split; [exact FROK|]; split; [exact FAL| exact NOFR]|].
      split; [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL ltac:(unfold USTACK_TOP; lia))|].
      split; [exact ST|]. split; [exact MI|].
      split; [exact (seg_ax_pres' _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU HWL CEIL ltac:(lia))|].
      split; [lia|]. split; [apply cnt_eq_refl|]. split; [apply refs_stable_refl|].
      split; [cbn [app]; exact FR|]. split; [cbn; lia|]. unfold uw_opt.
      eapply uw_chain_munch_nw; [exact UW | exact MU |]. constructor; [cbn; lia | constructor]. }
    pose proof EV0 as (OK & _).
    pose proof OK as (_ & _ & _ & _ & _ & _ & _ & _ & FROKK & _ & _).
    clear HEAP LS ST MI MU WM HWL WOK FR PRE PARTS.

    apply evt_done.
    eapply implA_bind.
    { eapply (BN_CTX_start_walkA) with (lo := lo) (OW := OW) (LB := LB) (PL := PL) (EA := EA);
        [| | | reflexivity | exact HPC | reflexivity].
      - eapply cenv_preA; [exact EV0 | exact LS0 | clear - LO' CSstart; lia | unfold MMFT_COST; clear - MCP CM0 CFW0; lia].
      - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EV0).
      - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_bn_mul_mont_fixed_top_227414 CTX).
    }
    cbv beta. intros [u1 ls1] Σ1 ms1 PO.
    apply (bn_postA_cpost LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -64) MMFT_COST Σ ls OW) in PO; [| exact OK | exact (proj1 (proj2 EV0))].
    cbn [fst snd] in *.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F1 & fc1 & m1 & OW1 & PL1 & -> & CP1 & (EPL1 & INCL1)).
    subst PL1. specialize (CP1 eq_refl).
    destruct (cenv_postA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -64) s0 ra (Some ras) MMFT_COST Σ ls OW m _ _ _ _ _ _ _ _ _ _ _ EV0 CP1) as (EV1 & LS1).
    pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP1) as RS1.
    rewrite (ret_pc_even 2258428) by (clear; lia).

    apply implA_from_evt. step. step.
    apply evt_done.
    eapply implA_bind.
    { eapply (BN_CTX_get_walkA) with (lo := lo) (OW := OW1) (LB := LB) (PL := PL) (EA := EA);
        [| | | reflexivity | exact HPC | reflexivity].
      - eapply cenv_preA; [exact EV1 | exact LS1 | clear - LO' CSget; lia | unfold MMFT_COST; clear - MCP CM0 CFW0; lia].
      - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EV1).
      - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_bn_mul_mont_fixed_top_22741c CTX).
    }
    cbv beta. intros [u2 ls2] Σ2 ms2 PO.
    apply (bn_postA_cpost LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -64) MMFT_COST Σ ls OW) in PO; [| exact OK | exact (proj1 (proj2 EV1))].
    cbn [fst snd] in *.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F2 & fc2 & m2 & OW2 & PL2 & -> & CP2 & (EPL2 & (ti & Et) & (at_ & HAt & ->) & INCL2)).
    subst PL2. specialize (CP2 eq_refl).
    destruct (cenv_postA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -64) s0 ra (Some ras) MMFT_COST Σ ls OW m _ _ _ _ _ _ _ _ _ _ _ EV1 CP2) as (EV2 & LS2).
    pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP2) as RS2.
    rewrite (ret_pc_even 2258436) by (clear; lia).
    pose proof (refs_stable_trans _ _ _ _ _ _ RS1 RS2) as RS02.
    pose proof (ref_at_stable _ _ _ _ PL _ _ RS02 HAr) as HAr2. pose proof (ref_at_stable _ _ _ _ PL _ _ RS02 HAa) as HAa2.
    pose proof (ref_at_stable _ _ _ _ PL _ _ RS02 HAb) as HAb2.
    pose proof (proj1 (proj2 EV2)) as HEAP2. pose proof (AH_nodup_l _ _ _ _ HEAP2) as ND2. pose proof (lib_state_h_parts _ _ _ _ _ _ LS2) as PARTS2.
    assert (NROt : u2 <> ROne) by (rewrite Et; unfold RPool, ROne, NFIX; lia).
    pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP2 PARTS2 FROKK HAt NROt) as (At0 & AtC & _).
    assert (AtR : 0 < at_ < 2^64) by (clear - At0 AtC C3; lia). clear AtC.
    unfold MallocRep.wz.
    apply implA_from_evt.

    step. if_cases KZ; rewrite ?unsigned_lit in KZ by (clear - AtR; lia); zify_cond KZ; [exfalso; clear - KZ AtR; lia| clear KZ].
    step. step.

    step. if_cases KE; rewrite ?unsigned_lit in KE by (clear - AaR AbR; lia); zify_cond KE.
    -
      assert (Eab : ra_ = rb).
      { destruct (Nat.eq_dec ra_ rb) as [E|NE]; [exact E| exfalso].
        pose proof (struct_disj Σ2 OW2 LB m2 HEAP2 ls2 PL EA _ _ PARTS2 FROKK ra_ rb aa ab NE HAa2 HAb2) as D. clear - D KE. lia. }
      subst rb. rewrite Nat.eqb_refl.
      step. step.
    apply evt_done.
    eapply implA_bind.
    { eapply (bn_sqr_fixed_top_walkA) with (lo := lo) (OW := OW2) (LB := LB) (PL := PL) (EA := EA);
        [| | | | reflexivity | exact HAt | exact HAa2 | rewrite Et; apply hpl_pool | exact NROb | first [exact NBa | exact NBb] | exact HPC | reflexivity | reflexivity | reflexivity].
      - eapply cenv_preA; [exact EV2 | exact LS2 | clear - LO'; lia | unfold MMFT_COST; clear - MCP CM0 CFW0; lia].
      - eapply cenv_roomA; [exact EV2 | exact ROOM | clear; lia].
      - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EV2).
      - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_bn_mul_mont_fixed_top_22745c CTX).
    }
    cbv beta. intros [u3 ls3] Σ3 ms3 PO.
    apply (bn_postA_cpost LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -64) MMFT_COST Σ ls OW) in PO; [| exact OK | exact (proj1 (proj2 EV2))].
    cbn [fst snd] in *.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F3 & fc3 & m3 & OW3 & PL3 & -> & CP3 & (EPL3 & ->)).
    subst PL3. specialize (CP3 eq_refl).
    destruct (cenv_postA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -64) s0 ra (Some ras) MMFT_COST Σ ls OW m _ _ _ _ _ _ _ _ _ _ _ EV2 CP3) as (EV3 & LS3).
    pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP3) as RS3.
    rewrite (ret_pc_even 2258500) by (clear; lia).
      apply implA_from_evt. step. if_true.

      step. step. step. step.
      pose proof (refs_stable_trans _ _ _ _ _ _ RS02 RS3) as RS03.
    apply evt_done.
    eapply implA_bind.
    { eapply (bn_from_montgomery_word_walkA) with (lo := lo) (OW := OW3) (LB := LB) (PL := PL) (EA := EA);
        [| | | reflexivity | exact (ref_at_stable _ _ _ _ PL _ _ RS03 HAr) | exact (ref_at_stable _ _ _ _ PL _ _ RS3 HAt) | exact WRr | rewrite Et; apply wref_pool | exact HPM | reflexivity | reflexivity | reflexivity].
      - eapply cenv_preA; [exact EV3 | exact LS3 | clear - LO'; lia | unfold MMFT_COST; clear - MCP CM0 CFW0; lia].
      - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EV3).
      - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_bn_mul_mont_fixed_top_22744c CTX).
    }
    cbv beta. intros [u4 ls4] Σ4 ms4 PO.
    apply (bn_postA_cpost LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -64) MMFT_COST Σ ls OW) in PO; [| exact OK | exact (proj1 (proj2 EV3))].
    cbn [fst snd] in *.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F4 & fc4 & m4 & OW4 & PL4 & -> & CP4 & (EPL4 & ->)).
    subst PL4. specialize (CP4 eq_refl).
    destruct (cenv_postA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -64) s0 ra (Some ras) MMFT_COST Σ ls OW m _ _ _ _ _ _ _ _ _ _ _ EV3 CP4) as (EV4 & LS4).
    pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP4) as RS4.
    rewrite (ret_pc_even 2258484) by (clear; lia).

      apply implA_from_evt. step. step. step. step.
    apply evt_done.
    eapply implA_post_evt.
    { eapply (BN_CTX_end_walkA) with (lo := lo) (OW := OW4) (LB := LB) (PL := PL) (EA := EA);
        [| reflexivity | exact HPC | reflexivity].
      - eapply cenv_preA; [exact EV4 | exact LS4 | clear - LO' CSend; lia | unfold MMFT_COST; clear - MCP CM0 CFW0; lia].
    }
    cbv beta. intros [u5 ls5] Σ5 ms5 PO.
    apply (bn_postA_cpost LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -64) MMFT_COST Σ ls OW) in PO; [| exact OK | exact (proj1 (proj2 EV4))].
    cbn [fst snd] in *.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F5 & fc5 & m5 & OW5 & PL5 & -> & CP5 & (EPL5 & EOW5)).
    subst PL5. specialize (CP5 eq_refl).
    destruct (cenv_postA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -64) s0 ra (Some ras) MMFT_COST Σ ls OW m _ _ _ _ _ _ _ _ _ _ _ EV4 CP5) as (EV5 & LS5).
    pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP5) as RS5.
    rewrite (ret_pc_even 2258516) by (clear; lia).
    destruct (cenv_finalA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -64) s0 ra (Some ras) MMFT_COST Σ ls OW m _ _ _ _ _ _ EV5 LS5 ltac:(unfold MMFT_COST; clear - MCP CM0 CFW0; lia)) as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
    pose proof EV5 as (_ & _ & STF & _ & _ & _ & _ & _ & FRF & _ & _). cbn [app] in FRF.
    step. do 8 step. release_frame FRF STF (bv_unsigned sp). step. step.
    apply evt_done. unfold bn_postA. do 17 eexists. exists m5, OW5, PL. split; [reflexivity|]. cbn [fst snd].
    split; [exact G1|]. split; [exact G2|]. split; [exact STF|]. split; [exact G3|]. split; [exact G4|]. split; [exact G5|]. split; [exact G6|]. split; [exact G7|].
    split; reflexivity.
    -
      assert (NE : ra_ <> rb).
      { intros E. subst rb. pose proof (ref_at_fun _ _ _ _ _ _ ND2 HAa2 HAb2) as EA_. clear - EA_ KE. lia. }
      replace ((ra_ =? rb)%nat) with false by (symmetry; apply Nat.eqb_neq; exact NE).
      step. step. step.
    apply evt_done.
    eapply implA_bind.
    { eapply (bn_mul_fixed_top_walkA) with (lo := lo) (OW := OW2) (LB := LB) (PL := PL) (EA := EA);
        [| | | reflexivity | exact HAt | exact HAa2 | exact HAb2 | rewrite Et; apply hpl_pool | exact NROb | exact NBa | exact NBb | exact HPC | reflexivity | reflexivity | reflexivity | reflexivity].
      - eapply cenv_preA; [exact EV2 | exact LS2 | clear - LO'; lia | unfold MMFT_COST; clear - MCP CM0 CFW0; lia].
      - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EV2).
      - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_bn_mul_mont_fixed_top_227438 CTX).
    }
    cbv beta. intros [u3 ls3] Σ3 ms3 PO.
    apply (bn_postA_cpost LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -64) MMFT_COST Σ ls OW) in PO; [| exact OK | exact (proj1 (proj2 EV2))].
    cbn [fst snd] in *.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F3 & fc3 & m3 & OW3 & PL3 & -> & CP3 & (EPL3 & ->)).
    subst PL3. specialize (CP3 eq_refl).
    destruct (cenv_postA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -64) s0 ra (Some ras) MMFT_COST Σ ls OW m _ _ _ _ _ _ _ _ _ _ _ EV2 CP3) as (EV3 & LS3).
    pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP3) as RS3.
    rewrite (ret_pc_even 2258464) by (clear; lia).
      apply implA_from_evt. step. if_false.

      step. step. step. step.
      pose proof (refs_stable_trans _ _ _ _ _ _ RS02 RS3) as RS03.
    apply evt_done.
    eapply implA_bind.
    { eapply (bn_from_montgomery_word_walkA) with (lo := lo) (OW := OW3) (LB := LB) (PL := PL) (EA := EA);
        [| | | reflexivity | exact (ref_at_stable _ _ _ _ PL _ _ RS03 HAr) | exact (ref_at_stable _ _ _ _ PL _ _ RS3 HAt) | exact WRr | rewrite Et; apply wref_pool | exact HPM | reflexivity | reflexivity | reflexivity].
      - eapply cenv_preA; [exact EV3 | exact LS3 | clear - LO'; lia | unfold MMFT_COST; clear - MCP CM0 CFW0; lia].
      - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EV3).
      - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_bn_mul_mont_fixed_top_22744c CTX).
    }
    cbv beta. intros [u4 ls4] Σ4 ms4 PO.
    apply (bn_postA_cpost LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -64) MMFT_COST Σ ls OW) in PO; [| exact OK | exact (proj1 (proj2 EV3))].
    cbn [fst snd] in *.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F4 & fc4 & m4 & OW4 & PL4 & -> & CP4 & (EPL4 & ->)).
    subst PL4. specialize (CP4 eq_refl).
    destruct (cenv_postA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -64) s0 ra (Some ras) MMFT_COST Σ ls OW m _ _ _ _ _ _ _ _ _ _ _ EV3 CP4) as (EV4 & LS4).
    pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP4) as RS4.
    rewrite (ret_pc_even 2258484) by (clear; lia).

      apply implA_from_evt. step. step. step. step.
    apply evt_done.
    eapply implA_post_evt.
    { eapply (BN_CTX_end_walkA) with (lo := lo) (OW := OW4) (LB := LB) (PL := PL) (EA := EA);
        [| reflexivity | exact HPC | reflexivity].
      - eapply cenv_preA; [exact EV4 | exact LS4 | clear - LO' CSend; lia | unfold MMFT_COST; clear - MCP CM0 CFW0; lia].
    }
    cbv beta. intros [u5 ls5] Σ5 ms5 PO.
    apply (bn_postA_cpost LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -64) MMFT_COST Σ ls OW) in PO; [| exact OK | exact (proj1 (proj2 EV4))].
    cbn [fst snd] in *.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F5 & fc5 & m5 & OW5 & PL5 & -> & CP5 & (EPL5 & EOW5)).
    subst PL5. specialize (CP5 eq_refl).
    destruct (cenv_postA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -64) s0 ra (Some ras) MMFT_COST Σ ls OW m _ _ _ _ _ _ _ _ _ _ _ EV4 CP5) as (EV5 & LS5).
    pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP5) as RS5.
    rewrite (ret_pc_even 2258516) by (clear; lia).
    destruct (cenv_finalA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -64) s0 ra (Some ras) MMFT_COST Σ ls OW m _ _ _ _ _ _ EV5 LS5 ltac:(unfold MMFT_COST; clear - MCP CM0 CFW0; lia)) as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
    pose proof EV5 as (_ & _ & STF & _ & _ & _ & _ & _ & FRF & _ & _). cbn [app] in FRF.
    step. do 8 step. release_frame FRF STF (bv_unsigned sp). step. step.
    apply evt_done. unfold bn_postA. do 17 eexists. exists m5, OW5, PL. split; [reflexivity|]. cbn [fst snd].
    split; [exact G1|]. split; [exact G2|]. split; [exact STF|]. split; [exact G3|]. split; [exact G4|]. split; [exact G5|]. split; [exact G6|]. split; [exact G7|].
    split; reflexivity.
  Qed.
End Proofs.

End WithRT.
