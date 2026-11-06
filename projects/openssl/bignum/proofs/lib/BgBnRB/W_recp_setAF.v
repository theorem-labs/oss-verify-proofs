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
From OSSVerify.Proofs.openssl.bignum.lib.BgB Require Import Layout R_unwind_chain RT_iface RT_client_kit D_defs I_lkit.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnMem BnTacX.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr ShiftPure.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnP Require Import BnLeaves.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import AsKit AsLoop.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require Import LibKitA ARun BnHeapA ImplA ImplAX UnwindA EdgesA AsStruct RtCallA W_cryptoA W_smallA AsStruct2.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require BnRepDefs BnRepA BnIfaceA.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepB Require Import BgRepDefs BgRep BgLayer BgIface.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BnDivWords BgWords BgArith BgMont.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require Import BnAKitAF BnCallAF W_expandAF W_callsAF W_copyAF W_small3A W_calls3AF ExpKitAF ExpBodyKitF.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import UbKit.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require Import UbStructF.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepB Require Import BgLayerF BgIfaceF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition ub_kind (pc : Z) : Z :=
  match pc with
  | 2868228 => 2
  | 2868232 => 1
  | 2868236 => 2
  | _ => 0
  end%Z.
Ltac ub := repeat (ub1 ub_kind).
Local Ltac ub_unfold ::= unfold BnHeapA.ACEIL in *.
Ltac hide_ors := repeat match goal with H : _ \/ _ |- _ => apply hide_intro in H end.
Ltac unhide := repeat match goal with H : hide _ |- _ => apply hide_elim in H end.
Definition BN_RECP_CTX_SET : Z := 0x2bc3c0.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Section Proofs.
  Variable CS : Z.
  Hypothesis CScopy : BN_COPY_STACK <= CS.
  Hypothesis CSnb : BN_NUM_BITS_STACK <= CS.
  Definition BN_RECP_CTX_SET_STACK : Z := 48 + CS.
  Definition BN_RECP_CTX_SET_COST : Z := MC.

  Ltac strip2 l := lazymatch l with
    | cons _ (cons _ nil) => constr:(@nil cell)
    | cons ?x ?t => let r := strip2 t in constr:(cons x r)
    end.

  Lemma nbits_range : forall b : bignum bptr, limbs (bn_buf b) -> 0 <= num_bits_pure b <= 64 * Z.of_nat (bn_top b).
  Proof.
    intros b HL. unfold num_bits_pure. destruct (Nat.eqb_spec (bn_top b) 0) as [E|NE]; [lia|].
    pose proof (limbs_nth (bn_buf b) (bn_top b - 1) HL) as LN. unfold limb, BW in LN.
    pose proof (num_bits_word_le (nth (bn_top b - 1) (bn_buf b) 0) 64 ltac:(lia) LN). lia.
  Qed.

  Lemma cenv_set_recpA : forall (LBx : list block) PLx EAx lox SPv FB (s0w raw : word) rasO TOTAL Σ0 (ls0 : bstate bptr) OW0 m0 pre used Σx (lsx : bstate bptr) mx mx' OWx c b bits sh,
    cenvA LBx PLx lox SPv FB s0w raw rasO TOTAL Σ0 ls0 OW0 m0 pre used Σx lsx mx OWx -> lib_state lsx mx OWx PLx EAx ->
    pl_recp PLx = Some c -> In b LBx -> blk_addr b <= c -> c + RECP_SC_SZ <= blk_addr b + blk_size b ->
    munch [(c, c + RECP_SC_SZ)]%Z mx mx' -> wmono bgbsegs mx mx' ->
    stk bgbsegs mx' lox FB -> mem_inv bgbsegs mx' ->
    rw_cells bgbsegs mx' c (recp_cells (set_recp bits sh lsx)) ->
    cenvA LBx PLx lox SPv FB s0w raw rasO TOTAL Σ0 ls0 OW0 m0 pre used Σx (set_recp bits sh lsx) mx' OWx /\ lib_state (set_recp bits sh lsx) mx' OWx PLx EAx.
  Proof.
    intros LBx PLx EAx lox SPv FB s0w raw rasO TOTAL Σ0 ls0 OW0 m0 pre used Σx lsx mx mx' OWx c b bits sh
           (OK & HEAP & ST & MI & AXP & CR & CNT & RS & FR & FSZ & UW) LS Ec Hb B1 B2 MU WM ST' MI' RC.
    pose proof OK as (CEIL & LOFB & FBSP & SPT & SP16 & FB16 & CNT0 & CRED0 & FROK & FAL & NOFR).
    pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN in *.
    assert (INB : In b (OWx ++ LBx)) by (apply in_or_app; right; exact Hb).
    pose proof (AH_range_gen _ _ _ _ b HEAP INB) as (B0 & _ & Bn & BC & BI).
    assert (AGO : agree_on (fun a => ~ (c <= a < c + RECP_SC_SZ)) mx mx').
    { eapply agree_on_mono; [apply (agree_on_of_munch _ _ _ MU WM)|]. intros a Ha. cbn [outside fst snd]. split; [exact Ha | exact I]. }
    assert (AGS : agree_on (fun a => FB <= a < USTACK_TOP) mx mx').
    { eapply agree_on_mono; [exact AGO|]. intros a Ha. cbv beta in *. unfold BnHeapA.ACEIL in *. lia. }
    split.
    - unfold cenvA. split; [exact OK|].
      split. { eapply (AH_frame Σx OWx LBx mx mx' _ HEAP MU WM). constructor; [|constructor]. right; right. exists b. split; [exact INB | cbn [fst snd]; lia]. }
      split; [exact ST'|]. split; [exact MI'|].
      split. { eapply ax_pres_trans; [exact AXP|]. unfold ax_pres. eapply agree_on_mono; [exact AGO|]. intros a [NX _] Hx. apply NX.
               unfold XW. apply rin_ivs_In. exists (c, c + RECP_SC_SZ). split; [apply in_or_app; right; apply pl_frames_recp; exact Ec | cbn [fst snd]; exact Hx]. }
      split; [exact CR|].
      split; [exact CNT|].
      split. { intros PL' i a Ha. apply ref_at_set_recp. exact (RS PL' i a Ha). }
      split. { eapply rw_cells_agree; [exact AGS | exact FR |]. intros a Ha. rewrite cells_size_app in Ha. cbn [cells_size csize Nat.add] in Ha. unfold USTACK_TOP in *. lia. }
      split; [exact FSZ|].
      unfold uw_opt in *. destruct rasO as [ras|]; [|exact I].
      apply (uw_chain_agree mx mx' ras SPv (bv_unsigned s0w) UW). eapply agree_on_mono; [exact AGS|]. intros a Ha. cbv beta in *. lia.
    - eapply (lib_state_set_recp Σx LBx SPv USTACK_TOP false [] lsx mx mx' OWx PLx EAx c bits sh); [exact HEAP| exact LS| exact FROK| exact Ec| exact MU| exact WM| exact RC].
  Qed.

  Lemma BN_RECP_CTX_set_walkA : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
      (lo : Z) (ras : list Z) (rd : bnref) (ad an : Z) (q : bptr),
    bn_preA Σ ls m OW LB PL EA sp lo BN_RECP_CTX_SET_STACK BN_RECP_CTX_SET_COST ->
    uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx BN_RECP_CTX_SET (bv_unsigned ra :: ras) ->
    tp = wz TP_A -> ref_at ls OW PL rd ad -> rd <> ROne -> recp_at PL an -> In (q, an, 64) LB -> an mod 8 = 0 -> a0 = wz an -> a1 = wz ad ->
    implA (BN_RECP_CTX_set (tree_ops bptr) rd ls) Σ
      (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA BN_RECP_CTX_SET_COST (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_RECP_CTX_SET) fc None m (seg_rom bgbsegs)).
  Proof.
    intros until q. intros PRE UW CTX -> HAd NROd HRC INQ AL8 -> ->.
    pose proof PRE as (HEAP & LS & FROK & ST & CEIL & LO & SPT & SP16 & MI & CNT & CRED & FAL & NOFR).
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
    pose proof LO as LO'. unfold BN_RECP_CTX_SET_STACK in LO'.
    pose proof MC0 as MCP.
    unfold BN_RECP_CTX_SET, MallocRep.wz.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
    pose proof (AH_nodup_l _ _ _ _ HEAP) as ND.
    pose proof (recp_at_refN ls OW PL an HRC) as HAN. pose proof (recp_at_refNr ls OW PL an HRC) as HANr.
    pose proof (recp_at_wrefN PL an HRC) as WRN. pose proof (recp_at_wrefNr PL an HRC) as WRNr. pose proof (recp_at_recp PL an HRC) as HRc.
    assert (INB : In (q, an, 64) (OW ++ LB)) by (apply in_or_app; right; exact INQ).
    pose proof (AH_range_gen _ _ _ _ _ HEAP INB) as (An0 & _ & _ & AnC & AnI). cbn [blk_addr blk_size fst snd] in An0, AnC, AnI.
    assert (AnR : 0 < an /\ an + 64 < 2^63) by (unfold BnHeapA.ACEIL in *; clear - An0 AnC C1 C2 C3; lia).
    destruct (AH_shb _ _ _ _ HEAP) as (SHB1 & SHB2).
    assert (CS16 : 16 <= CS) by (pose proof CSnb as H; unfold BN_NUM_BITS_STACK in H; clear - H; lia).
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgbsegs m) as WM.
    unfold BN_RECP_CTX_set, BN_num_bits, bbind, bget, bret, bunr. cbn [bind ret unreachable tree_ops tbind fst snd].
    apply implA_from_evt.

    carve_frame 48%nat ST. do 13 step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mP end.
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
    assert (HWL : Forall (w_lib ls OW PL lo (bv_unsigned sp)) [(bv_unsigned sp + -48, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
    assert (WOK : Forall (w_ok OW LB ls PL EA (bv_unsigned sp) []) [(bv_unsigned sp + -48, bv_unsigned sp)]).
    { constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia| constructor]. }
    pose proof (lib_state_frame Σ LB (bv_unsigned sp) USTACK_TOP [] ls m mP OW PL EA _ HEAP LS MU WM FROK WOK) as LS0.
    lazymatch type of FR with rw_cells _ _ _ ?fr => let p := strip2 fr in
      assert (EV0 : cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -48) s0 ra (Some ras) BN_RECP_CTX_SET_COST Σ ls OW m p 0 Σ ls mP OW) end.
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
    assert (LOFB16 : lo <= bv_unsigned sp + -48 - 16) by (clear - LO' CS16; lia).
    eapply (is_zero_callA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -48) s0 ra (Some ras) BN_RECP_CTX_SET_COST Σ ls OW m LOFB16); [exact EV0 | exact LS0 | exact HAd | exact NROd |].
    intros m9 y0A y1A y2A y4A y5A y6A y7A y8A y9A y10A y11A y12A y13A y14A EV9 LS9.
    rewrite (ret_pc_even 2868216) by (clear; lia).
    unfold is_zero_pure. destruct (Nat.eqb_spec (bn_top (getbn rd ls)) 0) as [TZ|TNZ]; cbn [Z.b2z].
    {
      step. if_false. apply evt_done. apply implA_unr. }
    step. if_true.

    hide_ors. ub. unhide.
    step. step. step.
    apply evt_done.
    eapply implA_bind.
    { eapply (BN_copy_walkA) with (lo := lo) (OW := OW) (LB := LB) (PL := PL) (EA := EA);
        [| | | reflexivity | exact HAN | exact HAd | exact WRN | exact NROd | reflexivity | reflexivity].
      - eapply cenv_preA; [exact EV9 | exact LS9 | clear - LO' CScopy; lia | unfold BN_RECP_CTX_SET_COST; clear - MCP; lia].
      - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EV9).
      - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_BN_RECP_CTX_set_2bc234 CTX).
    }
    cbv beta. intros [u1 ls1] Σ1 ms1 PO.
    apply (bn_postA_cpost LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -48) BN_RECP_CTX_SET_COST Σ ls OW) in PO; [| exact OK | exact (proj1 (proj2 EV9))].
    cbn [fst snd] in *.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F1 & fc1 & m1 & OW1 & PL1 & -> & CP1 & (EPL1 & -> & INCL1)).
    subst PL1. specialize (CP1 eq_refl).
    destruct (cenv_postA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -48) s0 ra (Some ras) BN_RECP_CTX_SET_COST Σ ls OW m _ _ _ _ _ _ _ _ _ _ _ EV9 CP1) as (EV1 & LS1).
    pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP1) as RS1.
    rewrite (ret_pc_even 2868252) by (clear; lia).
    unfold MallocRep.wz. apply implA_from_evt.
    step. if_cases KZ; rewrite ?unsigned_lit in KZ by (clear - AnR; lia); zify_cond KZ; [exfalso; clear - KZ AnR; lia| clear KZ].

    unfold BN_zero, bbind, bget, bset. cbn [bind ret tree_ops tbind fst snd].
    step. step.
    eapply (zero_callA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -48) s0 ra (Some ras) BN_RECP_CTX_SET_COST Σ ls OW m LOFB16) with (r := RRecpNr) (ar := an + 24); [exact EV1 | exact LS1 | exact (recp_at_refNr _ _ _ _ HRC) | exact WRNr |].
    intros mB z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 lsB EVB LSB.
    rewrite (ret_pc_even 2868264) by (clear; lia).

    assert (HAdB : ref_at lsB OW1 PL rd ad) by (apply ref_at_setbn; exact (ref_at_stable _ _ _ _ PL _ _ RS1 HAd)).
    pose proof (st_wf_ok _ _ (proj1 (lib_state_h_parts _ _ _ _ _ _ LSB)) (ref_at_valid _ _ _ _ _ _ _ _ LSB HAdB) NROd) as (OKd1 & OKd2 & OKd3 & OKd4).
    set (bd := getbn rd lsB) in *. unfold BG_DMAX in OKd3.
    assert (CTd : Z.land (bn_flags bd) 4 = 0) by (destruct OKd4 as [E|E]; rewrite E; reflexivity).
    step. step.
    eapply (num_bits_callA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -48) s0 ra (Some ras) BN_RECP_CTX_SET_COST Σ ls OW m); [exact EVB | exact LSB | exact HAdB | exact NROd | unfold BN_NUM_BITS_STACK in *; clear - LO' CSnb; lia |].
    intros mC y0C y1C y2C y4C y5C y6C y7C y8C y9C y10C y11C y12C y13C y14C EVC LSC.
    rewrite (ret_pc_even 2868272) by (clear; lia).
    pose proof (nbits_range bd OKd1) as BITS.
    unfold has_flag, BN_FLG_CONSTTIME. fold bd. rewrite CTd. cbn [Z.eqb negb tbind]. cbv beta.
    set (nb := num_bits_pure bd) in *.

    pose proof (lib_state_recp_cells _ _ _ _ _ _ _ _ LSC HRc) as RC. unfold recp_cells in RC.
    pose proof EVC as (_ & HEAPC & STC & MIC & _).
    pose proof (proj2 (AH_acc _ _ _ _ (q, an, 64) HEAPC ltac:(apply in_or_app; right; exact INQ))) as ACCR. cbn [blk_addr blk_size fst snd] in ACCR.
    pose proof (AH_offsh _ _ _ _ (q, an, 64) HEAPC ltac:(apply in_or_app; right; exact INQ)) as OFFR. cbn [blk_addr blk_size fst snd] in OFFR. unfold SHLO, SHHI in OFFR.
    assert (AnT : 0 <= an /\ an + 64 <= 140737488355328) by (unfold BnHeapA.ACEIL in *; clear - An0 AnC C1 C2 C3; lia).
    pose proof (munch_refl [(an + 48, an + 48 + RECP_SC_SZ)]%Z mC) as MUR. pose proof (wmono_refl bgbsegs mC) as WMR. unfold RECP_SC_SZ in MUR.
    do 3 step. shl_with ACCR AL8. chk0.
    step.
    do 3 step. shl_with ACCR AL8. chk0.
    step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m8 end.
    destruct (cenv_set_recpA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -48) s0 ra (Some ras) BN_RECP_CTX_SET_COST Σ ls OW m _ _ _ _ mC m8 _ (an + 48) (q, an, 64) nb 0 EVC LSC HRc INQ
                ltac:(cbn [blk_addr fst snd]; clear; lia) ltac:(cbn [blk_addr blk_size fst snd]; unfold RECP_SC_SZ; clear; lia) MUR WMR STC MIC RC) as (EV8 & LS8).
    step.
    apply evt_done. unfold bsetrecp. cbn [ret tree_ops]. apply implA_ret_evt.
    destruct (cenv_finalA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -48) s0 ra (Some ras) BN_RECP_CTX_SET_COST Σ ls OW m _ _ _ _ _ _ EV8 LS8 ltac:(unfold BN_RECP_CTX_SET_COST; clear - MCP; lia)) as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
    pose proof EV8 as (_ & _ & STF & _ & _ & _ & _ & _ & FRF & _ & _). cbn [app] in FRF.
    do 5 step. release_frame FRF STF (bv_unsigned sp). step. step.
    apply evt_done. unfold bn_postA. do 17 eexists. exists m8, OW1, PL. split; [reflexivity|]. cbn [fst snd].
    split; [exact G1|]. split; [exact G2|]. split; [exact STF|]. split; [exact G3|]. split; [exact G4|]. split; [exact G5|]. split; [exact G6|]. split; [exact G7|].
    split; reflexivity.
  Qed.
End Proofs.

End WithRT.
