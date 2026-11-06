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
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Malloc Prog BnBase BnDivWords BnWords BnWordsCorrect BnModel BnTree BnInv BnSpecs BnMInv BgState BgInv BgLib BgWords BgArith BgMont BgExp.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgB Require Import Layout R_unwind_chain RT_iface RT_iface2 RT_client_kit D_defs I_lkit.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnMem BnTacX.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import MState Mem Cells Step Arr Bytes Frame.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr ShiftPure.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnP Require Import BnLeaves.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import AsKit AsLoop.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require Import LibKitA ARun BnHeapA ImplA ImplAX UnwindA EdgesA AsStruct RtCallA W_cryptoA W_smallA AsStruct2.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require BnRepDefs BnRepA BnIfaceA.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepB Require Import BgRepDefs BgRep BgLayer BgIface.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require Import W_ctxA W_ctx_getA W_ctx_endA.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require Import AFrameKit AFrameCall AFrameTac AFrameEnv BnAKitAF BnCallAF W_expandAF W_callsAF W_ctxAF W_ctx_getAF W_ctx_endAF W_copyAF W_lshiftAF W_div_tailAF W_divAF W_bndivAF W_uaddAF W_addAF W_subAF W_set_wordAF AFrameComp ExpKitAF W_small3A W_calls3AF W_nnmodAF ExpStmtF ExpBodyKitF PlaceRecpA RecpKitAF W_recp_initAF W_recp_freeAF W_recp_setAF InvKitAF Fr_exp_recp.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnE Require W_gueron_arr.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import UbKit.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require Import UbStructF.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepB Require Import BgLayerF BgIfaceF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition ub_kind (pc : Z) : Z :=
  match pc with
  | 2860232 => 2
  | 2860236 => 1
  | 2860240 => 2
  | 2860292 => 2
  | 2860296 => 1
  | 2860300 => 2
  | 2860608 => 2
  | 2860712 => 2
  | 2860816 => 2
  | 2860860 => 1
  | 2860864 => 2
  | 2860896 => 1
  | 2860900 => 2
  | 2860904 => 1
  | 2860908 => 1
  | 2860912 => 2
  | 2860992 => 2
  | 2861048 => 1
  | 2861056 => 2
  | 2861064 => 1
  | 2861068 => 2
  | 2861132 => 2
  | _ => 0
  end%Z.
Ltac ub := repeat (ub1 ub_kind).
Local Ltac ub_unfold ::= unfold BnHeapA.ACEIL in *.
Ltac hide_ors := repeat match goal with H : _ \/ _ |- _ => apply hide_intro in H end.
Ltac unhide := repeat match goal with H : hide _ |- _ => apply hide_elim in H end.

Lemma swrap32_of_u64 : forall x, -2147483648 <= x < 2147483648 -> bv_swrap 32 (bv_unsigned (Z_to_bv 64 x) + 0) = x.
Proof.
  intros x H. rewrite Z.add_0_r, Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
  destruct (Z.lt_ge_cases x 0) as [N|P].
  - replace (x mod 18446744073709551616) with (x + 18446744073709551616) by (apply Z.mod_unique with (-1); lia).
    rewrite swrap32_plus_2_64. apply bn_swrap32_small. lia.
  - rewrite Z.mod_small by lia. apply bn_swrap32_small. lia.
Qed.

Lemma ub_shl_ok : forall wv k, 0 <= k <= 6 -> 0 <= wv < 2 ^ 25 ->
  bv_swrap 32 (bv_wrap 32 wv ≫ (Z.lxor k 18446744073709551615 mod 32)) = 0.
Proof.
  intros wv k Hk Hw. rewrite (W_gueron_arr.g_lxor_ones64 k) by lia.
  replace ((18446744073709551615 - k) mod 32) with (31 - k) by (Z.div_mod_to_equations; lia).
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32) with 4294967296. rewrite (Z.mod_small wv) by lia.
  rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small; [reflexivity|].
  split; [lia|]. apply Z.lt_le_trans with (2 ^ 25); [lia|]. apply Z.pow_le_mono_r; lia.
Qed.

Section Body.
Context {AR1 : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR1).
Local Notation AF := (@ar_AF AR1).
Local Notation PMc := (@ar_PMc AR1).
Local Notation ACEIL := (@BnHeapA.ACEIL AR1).
Local Notation AHEAP := (@BnHeapA.AHEAP AR1).

Section Proofs.

  Variables (CS CSL CMM : Z).
  Hypothesis CSstart : BN_CTX_START_STACK <= CS.
  Hypothesis CSget : BN_CTX_GET_STACK <= CS.
  Hypothesis CSend : BN_CTX_END_STACK <= CS.
  Hypothesis CSnnmod : BN_NNMOD_STACK <= CS.
  Hypothesis CSsetw : BN_SET_WORD_STACK <= CS.
  Hypothesis CSnb : BN_NUM_BITS_STACK <= CS.
  Hypothesis CScopy : BN_COPY_STACK <= CS.
  Hypothesis CSLcopy : BN_COPY_STACK <= CSL.
  Hypothesis CSLnb : BN_NUM_BITS_STACK <= CSL.
  Hypothesis CSset : BN_RECP_CTX_SET_STACK CSL <= CS.
  Hypothesis CSinit : RECP_INIT_STACK <= CS.
  Hypothesis CSfree : RECP_FREE_STACK <= CS.
  Hypothesis CMM0 : 0 <= CMM.

  Hypothesis BN_mod_mul_reciprocal_walkA : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
      (lo : Z) (ras : list Z) (rr rx ry : bnref) (ar ax ay an ac : Z) (qc : bptr) (q : bptr),
    bn_preA Σ ls m OW LB PL EA sp lo CS CMM ->
    fr_room 1 ls OW LB ->
    uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx 0x2bc4a8 (bv_unsigned ra :: ras) ->
    tp = wz TP_A -> ref_at ls OW PL rr ar -> ref_at ls OW PL rx ax -> ref_at ls OW PL ry ay -> hpl PL rr -> rx <> ROne -> ry <> ROne -> nbuf PL rx -> nbuf PL ry ->
    recp_at PL an -> In (q, an, 64) LB -> an mod 8 = 0 -> pl_ctx PL = Some (ac, qc) ->
    a0 = wz ar -> a1 = wz ax -> a2 = wz ay -> a3 = wz an -> a4 = wz ac ->
    implA (BN_mod_mul_reciprocal (tree_ops bptr) rr rx ry ls) Σ
      (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA CMM (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0x2bc4a8) fc None m (seg_rom bgbsegs)).

  Definition EXP_RECP_TOTAL : Z := 37 * MC + BN_NNMOD_COST + 65569 * CMM.

  Section Fixed.

    Variable Q : unit * bstate bptr -> rts RT -> machine_state -> Prop.
    Variables (sp gp s0 ra : word) (Σ1 : rts RT) (ls : bstate bptr) (m1 : mem) (OW LB : list block) (PL0 : placement) (EA : BnRepDefs.err_addrs).
    Variables (lo spa f TOTAL : Z) (q1 q2 : bptr) (ras : list Z) (g : nat) (junk : list byte).
    Variables (rr ra_ rp rm : bnref) (arr ara arp arm ac : Z) (qc : bptr).
    Local Notation LBX := ((q1, f + 32, 256) :: (q2, f + 352, 64) :: LB).
    Local Notation CENV0 := (cenvA LBX PL0 lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls OW).
    Hypothesis TOTAL_OK : EXP_RECP_TOTAL <= TOTAL.
    Hypothesis LOK : lo <= spa - CS.
    Hypothesis ROOM : fr_room 1 ls OW LBX.
    Hypothesis INF : In (f, 3%nat) (@ar_FR AR1).
    Hypothesis NFV : forall x, f + 32 <= x < f + 416 -> ~ rin_ivs (pl_frames PL0) x.
    Hypothesis CTX : uk_ctx BN_MOD_EXP_RECP (bv_unsigned ra :: ras).
    Hypothesis HPC : pl_ctx PL0 = Some (ac, qc).
    Hypothesis HFN : pl_bn PL0 RRecpN = None.
    Hypothesis HFNr : pl_bn PL0 RRecpNr = None.
    Hypothesis HFR : pl_recp PL0 = None.
    Hypothesis PWF0 : pl_wf PL0.
    Hypothesis HAr : ref_at ls OW PL0 rr arr.
    Hypothesis HAa : ref_at ls OW PL0 ra_ ara.
    Hypothesis HAp : ref_at ls OW PL0 rp arp.
    Hypothesis HAm : ref_at ls OW PL0 rm arm.
    Hypothesis WRr : hpl PL0 rr.
    Hypothesis NROa : ra_ <> ROne.
    Hypothesis NROp : rp <> ROne.
    Hypothesis NROm : rm <> ROne.
    Hypothesis NBa : nbuf PL0 ra_.

    Definition locs (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 : word) : list cell :=
      [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 (Z_to_bv 64 f)].

    Hypothesis CONT : forall (Σk : rts RT) (lsk : bstate bptr) (mk : mem) (OWk : list block) (loc : list cell) (used : Z) (mb : mem)
          (x1 x5 x6 x7 x9 y10 y11 y12 y13 y14 y15 y16 y17 x20 x21 x22 rv x25 x26 x27 x28 x29 x30 x31 : word) (Fk : bvmap 5 word) (fck : bv 32),
        CENV0 mb (loc ++ [CB g junk]) used Σk lsk mk OWk ->
        lib_state lsk mk OWk PL0 EA -> used <= TOTAL -> ax_pres LB (bv_unsigned sp) (XW PL0) m1 mb -> rv = wz 1 ->
        implA (TRet (tt, lsk)) Σk Q
          (MS (mkR x1 (Z_to_bv 64 spa) gp (wz TP_A) x5 x6 x7 sp x9 y10 y11 y12 y13 y14 y15 y16 y17
                   (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) x20 x21 x22 (Z_to_bv 64 f) rv x25 x26 x27 x28 x29 x30 x31)
              Fk (wz EXP_RECP_EXIT) fck None mk (seg_rom bgbsegs)).

    Lemma MC0 : 0 <= MC. Proof. unfold MC. lia. Qed.

    Ltac lstep v := step;
      lazymatch goal with
      | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ _) _) => change (Z_to_le_bytes 8 v) with (le8 (Z_to_bv 64 v)); mem_after_store
      | |- _ => idtac
      end.

    Ltac fgeo HEAP :=
      destruct (AH_fr_geo _ _ _ _ f 3%nat HEAP INF) as (G1 & G2 & G3 & G4 & G5); unfold fs_size in G3, G5;
      change (Z.shiftl 64 (Z.of_nat 3)) with 512 in G3, G5; unfold SEGTOP_A, STACK_WIN, BnHeapA.ACEIL in *.

    Ltac solve_loc := lazymatch goal with |- exists loc, ?l = loc ++ _ => exists (removelast l); reflexivity end.

    Ltac strip2 l := lazymatch l with
      | cons _ (cons _ nil) => constr:(@nil cell)
      | cons ?x ?t => let r := strip2 t in constr:(cons x r)
      end.

    Ltac relocal EV LS MU WM ST MI FR FSZ EV' LS' :=
      unfold locs in FSZ; cbn [app cells_size csize Nat.add] in FSZ;
      lazymatch type of FR with rw_cells _ _ _ ?fr => let p := strip2 fr in
        destruct (cenv_localA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p _ _ _ _ _ _ _ _ EV LS MU WM ltac:(clear; lia) ltac:(clear - FSZ; lia) ST MI FR
                    ltac:(cbn [cells_size csize Nat.add app]; clear - FSZ; lia)) as (EV' & LS') end.

    Local Ltac kit EV :=
      pose proof EV as (OK & _);
      pose proof OK as (CEIL & LOFB & FBSP & SPT & SP16 & FB16 & _ & _ & FROKK & _ & _);
      pose proof (ESPvA _ _ _ _ _ _ _ _ _ _ _ _ OK (proj1 (proj2 EV))) as ESP;
      pose proof (AH_ceil _ _ _ _ (proj1 (proj2 EV))) as (C1 & C2 & C3); unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3;
      assert (CS16 : 16 <= CS) by (pose proof CSend as H; unfold BN_CTX_END_STACK in H; clear - H; lia);
      assert (LOFB16 : lo <= spa - 16) by (clear - LOK CS16; lia);
      pose proof MC0 as MCP.

    Lemma sx32_int : forall z, -2147483648 <= z < 2147483648 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
    Proof.
      intros z Hz. unfold sx32. f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
      replace (z mod 18446744073709551616) with (z mod 18446744073709551616 + 0) by lia. rewrite bn_swrap32_mod by lia. lia.
    Qed.
    Lemma NROr : rr <> ROne. Proof. exact (proj1 (hpl_wref _ _ WRr)). Qed.
    Lemma NNr : rr <> RRecpN /\ rr <> RRecpNr. Proof. exact (ref_at_not_recp ls OW PL0 rr arr HFN HFNr HAr). Qed.
    Lemma NNa : ra_ <> RRecpN /\ ra_ <> RRecpNr. Proof. exact (ref_at_not_recp ls OW PL0 ra_ ara HFN HFNr HAa). Qed.
    Lemma NNp : rp <> RRecpN /\ rp <> RRecpNr. Proof. exact (ref_at_not_recp ls OW PL0 rp arp HFN HFNr HAp). Qed.
    Lemma NNm : rm <> RRecpN /\ rm <> RRecpNr. Proof. exact (ref_at_not_recp ls OW PL0 rm arm HFN HFNr HAm). Qed.

    Section Scope.
      Local Notation AN := (f + 352).
      Local Notation PL := (pl_place_recp PL0 (f + 352)).
      Local Notation CENV := (cenvA LBX PL lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls OW).

      Lemma HPCP : pl_ctx PL = Some (ac, qc). Proof. exact HPC. Qed.
      Lemma HRC : recp_at PL AN. Proof. apply recp_at_place. Qed.
      Lemma HArP : ref_at ls OW PL rr arr. Proof. apply ref_at_place_recp; [exact (proj1 NNr) | exact (proj2 NNr) | exact HAr]. Qed.
      Lemma HAaP : ref_at ls OW PL ra_ ara. Proof. apply ref_at_place_recp; [exact (proj1 NNa) | exact (proj2 NNa) | exact HAa]. Qed.
      Lemma HApP : ref_at ls OW PL rp arp. Proof. apply ref_at_place_recp; [exact (proj1 NNp) | exact (proj2 NNp) | exact HAp]. Qed.
      Lemma HAmP : ref_at ls OW PL rm arm. Proof. apply ref_at_place_recp; [exact (proj1 NNm) | exact (proj2 NNm) | exact HAm]. Qed.
      Lemma WRrP : hpl PL rr.
      Proof. destruct WRr as [N H]. split; [exact N|]. intros p E. rewrite (pl_of_place_recp_other PL0 AN rr (proj1 NNr) (proj2 NNr)) in E. exact (H p E). Qed.
      Lemma NBr : nbuf PL rr. Proof. exact (hpl_nbuf _ _ WRrP). Qed.
      Lemma NBaP : nbuf PL ra_.
      Proof. intros a d. rewrite (pl_of_place_recp_other PL0 AN ra_ (proj1 NNa) (proj2 NNa)). exact (NBa a d). Qed.
      Lemma NBN : nbuf PL RRecpN. Proof. intros a d. rewrite pl_of_place_recp_N. discriminate. Qed.
            Lemma INQ2 : In (q2, AN, 64) LBX. Proof. right; left; reflexivity. Qed.

      Lemma NFVP : forall x, f + 32 <= x < f + 288 -> ~ rin_ivs (pl_frames PL) x.
      Proof.
        intros x Hx HR. apply rin_ivs_In in HR. destruct HR as (iv & Hin & Hr). apply pl_frames_place_recp_In in Hin.
        destruct Hin as [->|[->|[->|Hin]]]; cbn [fst snd] in Hr; try (clear - Hx Hr; lia).
        apply (NFV x ltac:(clear - Hx; lia)). apply rin_ivs_In. exists iv. split; assumption.
      Qed.

      Lemma ax_unplace : forall mb pre used Σ (lsx : bstate bptr) m OWx mm mm',
        CENV mb pre used Σ lsx m OWx ->
        ax_pres ((q2, AN, 64) :: LB) (bv_unsigned sp) (XW PL) mm mm' -> ax_pres LB (bv_unsigned sp) (XW PL0) mm mm'.
      Proof.
        intros mb pre used Σ lsx m OWx mm mm' (OK & HEAP & _) AX.
        pose proof OK as (CEIL & LOFB & FBSP & _).
        assert (HbA : In (q2, AN, 64) (OWx ++ LBX)) by (apply in_or_app; right; right; left; reflexivity).
        pose proof (AH_range_gen _ _ _ _ _ HEAP HbA) as (B0 & _ & _ & BC & BI). cbn [blk_addr blk_size fst snd] in B0, BC, BI.
        pose proof (ax_pres_outer [(q2, AN, 64)] LB _ _ _ _ AX) as AXT.
        eapply agree_on_mono; [exact AXT|]. intros x [NX Hc]. split; [| exact Hc].
        intros HX. apply xw_place_recp in HX. destruct HX as [HX|HX]; [exact (NX HX)|].
        destruct Hc as [Hc|[Hc|(b' & Hb' & Hr)]].
        + unfold BnHeapA.ACEIL in *. clear - Hc HX BC CEIL LOFB FBSP. lia.
        + destruct Hc as [(l & h & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin.
          destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; clear - Hr HX BI; lia.
        + assert (NE : blk_id (q2, AN, 64) <> blk_id b').
          { intros E. pose proof (AH_nodup _ _ _ _ HEAP) as ND. rewrite map_app in ND. apply NoDup_app_remove_l in ND. cbn [map] in ND.
            inversion ND as [|? ? _ ND2]. inversion ND2 as [|? ? NI _]. apply NI. rewrite E. apply in_map. exact Hb'. }
          pose proof (AH_disjoint_gen _ _ _ _ (q2, AN, 64) b' HEAP HbA ltac:(apply in_or_app; right; right; right; exact Hb') NE) as DJ.
          cbn [blk_addr blk_size fst snd] in DJ. clear - DJ Hr HX. lia.
      Qed.

      Lemma exit_tail : forall mb pre used ΣK lsK mK OWK (w0 w1 w2 w3 w4 w5 w6 w8 w9 : word)
          (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x21 x22 x25 x26 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
        CENV mb pre used ΣK lsK mK OWK -> pre = locs w0 w1 w2 w3 w4 w5 w6 (Z_to_bv 64 AN) w8 w9 ++ [CB g junk] -> lib_state lsK mK OWK PL EA -> used <= TOTAL ->
        ax_pres LB (bv_unsigned sp) (XW PL0) m1 mb ->
        implA (tbind (BN_CTX_end (tree_ops bptr) lsK) (fun p => BN_RECP_CTX_free (tree_ops bptr) (snd p))) ΣK Q
          (MS (mkR x1 (Z_to_bv 64 spa) gp (wz TP_A) t0 t1 t2 sp (Z_to_bv 64 spa) a0 a1 a2 a3 a4 a5 a6 a7
                   (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) (Z_to_bv 64 ac) x21 x22 (Z_to_bv 64 f) (Z_to_bv 64 1) x25 x26 (Z_to_bv 64 AN) t3 t4 t5 t6)
              F (Z_to_bv 64 2861208) fc None mK (seg_rom bgbsegs)).
      Proof.
        intros until fc. intros EVK -> LSK USED AXB. kit EVK. unfold MallocRep.wz in *.
        pose proof (lib_state_h_parts _ _ _ _ _ _ LSK) as (_ & PWFK & _).
        apply implA_from_evt. step. step.
    apply evt_done.
        eapply implA_bind.
        { eapply (BN_CTX_end_walkA) with (lo := lo) (OW := OWK) (LB := ((q1, f + 32, 256) :: (q2, f + 352, 64) :: LB)) (PL := PL) (EA := EA);
            [| reflexivity | exact HPCP | reflexivity].
          - eapply cenv_preA; [exact EVK | exact LSK | clear - LOK CSend; lia | clear - USED; lia].
        }
        cbv beta. intros [uE lsE] ΣE msE PO.
        apply (bn_postA_cpost ((q1, f + 32, 256) :: (q2, f + 352, 64) :: LB) PL EA lo (bv_unsigned sp) spa TOTAL Σ1 ls OW) in PO; [| exact OK | exact (proj1 (proj2 EVK))].
        cbn [fst snd] in *.
        destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & FE & fcE & mE & OWE & PLE & -> & CPE & (EPLE & EOWE)).
        subst PLE. specialize (CPE eq_refl).
        destruct (cenv_postA ((q1, f + 32, 256) :: (q2, f + 352, 64) :: LB) PL EA lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls OW mb _ _ _ _ _ _ _ _ _ _ _ EVK CPE) as (EVE & LSE).
        pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CPE) as RSE. clear CPE.
        rewrite (ret_pc_even 2861216) by (clear; lia).
        cbv beta. cbn [fst snd]. destruct uE.
        pose proof EVE as (_ & _ & _ & _ & _ & _ & _ & _ & FRE & _). cbn [app locs] in FRE.
        apply implA_from_evt. step. step.
        fgeo (proj1 (proj2 EVE)).
        apply evt_done.
        eapply (recp_free_lastA Q [(q1, f + 32, 256); (q2, f + 352, 64)] LB PL0 EA lo (bv_unsigned sp) spa s0 ra ras TOTAL Σ1 ls OW mb _ (used + 0) ΣE lsE mE OWE q2 (f + 352));
          [exact EVE | exact LSE | right; left; reflexivity | clear - G2; Z.div_mod_to_equations; lia | exact PWF0 | exact HFN | exact HFNr | exact HFR | reflexivity
          | clear - LOK CSfree; lia | clear - USED; lia | reflexivity | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_BN_mod_exp_recp_2ba6c0 CTX) |].
        intros Σ' ls' m' OW' y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 F' fc' EV' LS' AXO.
        rewrite (ret_pc_even 2861224) by (clear; lia).
        apply implA_from_evt. step.
        apply evt_done. eapply CONT; [exact EV' | exact LS' | clear - USED; lia | exact (ax_pres_trans _ _ _ _ _ _ AXB AXO) | reflexivity].
      Qed.

      Definition bst (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x24 x25 x27 t3 t4 t5 t6 : word) (F : bvmap 5 word) (pc : Z) (fc : bv 32) (m : mem) : machine_state :=
        MS (mkR x1 (Z_to_bv 64 spa) gp (Z_to_bv 64 TP_A) t0 t1 t2 sp (Z_to_bv 64 spa) a0 a1 a2 a3 a4 a5 a6 a7
                (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) (Z_to_bv 64 ac) (Z_to_bv 64 arr) (Z_to_bv 64 arp) (Z_to_bv 64 f) x24 x25 (Z_to_bv 64 SHB) x27 t3 t4 t5 t6)
           F (Z_to_bv 64 pc) fc None m (seg_rom bgbsegs).

      Local Notation MUL := (BN_mod_mul_reciprocal (tree_ops bptr)).

      Local Ltac kitg EV := kit EV;
        destruct (AH_fr_geo _ _ _ _ f 3%nat (proj1 (proj2 EV)) INF) as (G1 & G2 & G3 & G4 & G5); unfold fs_size in G3, G5;
        change (Z.shiftl 64 (Z.of_nat 3)) with 512 in G3, G5; unfold SEGTOP_A, STACK_WIN, BnHeapA.ACEIL in *;
        assert (AL8 : (f + 352) mod 8 = 0) by (clear - G2; Z.div_mod_to_equations; lia);
        assert (ALV : (f + 32) mod 8 = 0) by (clear - G2; Z.div_mod_to_equations; lia).

      Definition SQRQ (mb : mem) (pre : list cell) (used0 : Z) (lsK : bstate bptr) (OWK : list block) (x25 x27 : word)
          (r : unit * bstate bptr) (Σ' : rts RT) (ms' : machine_state) : Prop :=
        exists mK' OWK' used' (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc,
          ms' = bst x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) x25 x27 t3 t4 t5 t6 F 2861048 fc mK'
          /\ CENV mb pre used' Σ' (snd r) mK' OWK' /\ lib_state (snd r) mK' OWK' PL EA /\ refs_stable lsK OWK (snd r) OWK' /\ used' <= used0.

      Lemma sqr_loopA : forall c mb pre used ΣK lsK mK OWK (x25 x27 : word) (w0 w1 w2 w3 w4 w5 w6 w8 w9 : word)
          (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
        CENV mb pre used ΣK lsK mK OWK -> pre = locs w0 w1 w2 w3 w4 w5 w6 (Z_to_bv 64 AN) w8 w9 ++ [CB g junk] -> lib_state lsK mK OWK PL EA ->
        ref_at lsK OWK PL rr arr -> Z.of_nat (S c) < 2 ^ 31 ->
        used + Z.of_nat (S c) * CMM <= TOTAL ->
        implA (exp_sqr_loop (tree_ops bptr) MUL (S c) rr lsK) ΣK (SQRQ mb pre (used + Z.of_nat (S c) * CMM) lsK OWK x25 x27)
          (bst x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (Z.of_nat (S c))) x25 x27 t3 t4 t5 t6 F 2861012 fc mK).
      Proof.
        induction c as [|c IH]; intros until fc; intros EVK EPRE LSK HArK CBN KCOST; kitg EVK; unfold bst, MallocRep.wz in *;
          pose proof EVK as (_ & _ & _ & _ & _ & _ & _ & _ & FRK & _); rewrite EPRE in FRK; cbn [app locs] in FRK;
          rewrite exp_sqr_loop_S; apply implA_from_evt; do 5 step; step.
        -
    apply evt_done.
          eapply implA_bind.
          { eapply (BN_mod_mul_reciprocal_walkA) with (lo := lo) (OW := OWK) (LB := ((q1, f + 32, 256) :: (q2, f + 352, 64) :: LB)) (PL := PL) (EA := EA);
              [| | | | reflexivity | exact HArK | exact HArK | exact HArK | exact WRrP | exact NROr | exact NROr | exact NBr | exact NBr | exact HRC | exact INQ2 | exact AL8 | exact HPCP | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity].
            - eapply cenv_preA; [exact EVK | exact LSK | clear - LOK; lia | clear - KCOST CMM0; lia].
            - eapply cenv_roomA; [exact EVK | exact ROOM | clear; lia].
            - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EVK).
            - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_BN_mod_exp_recp_2ba604 CTX).
          }
          cbv beta. intros [us lss] Σs mss PO.
          apply (bn_postA_cpost ((q1, f + 32, 256) :: (q2, f + 352, 64) :: LB) PL EA lo (bv_unsigned sp) spa TOTAL Σ1 ls OW) in PO; [| exact OK | exact (proj1 (proj2 EVK))].
          cbn [fst snd] in *.
          destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & Fs & fcs & ms & OWs & PLs & -> & CPs & (EPLs & ->)).
          subst PLs. specialize (CPs eq_refl).
          destruct (cenv_postA ((q1, f + 32, 256) :: (q2, f + 352, 64) :: LB) PL EA lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls OW mb _ _ _ _ _ _ _ _ _ _ _ EVK CPs) as (EVs & LSs).
          pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CPs) as RSs. clear CPs.
          rewrite (ret_pc_even 2861036) by (clear; lia).
          unfold MallocRep.wz. apply implA_from_evt. step. if_false.
          step. rewrite unsigned_lit by (clear - CBN; lia). rewrite (bn_swrap32_small _) by (clear - CBN; lia).
          rewrite exp_sqr_loop_O. change (Z.of_nat 1 + -1) with 0.
          step. if_false.
          apply evt_done. apply implA_ret.
          unfold SQRQ, bst. exists ms, OWs, (used + CMM). do 18 eexists. split; [reflexivity|]. cbn [fst snd].
          split; [exact EVs|]. split; [exact LSs|]. split; [exact RSs|]. clear - CMM0. lia.
        -
    apply evt_done.
          eapply implA_bind.
          { eapply (BN_mod_mul_reciprocal_walkA) with (lo := lo) (OW := OWK) (LB := ((q1, f + 32, 256) :: (q2, f + 352, 64) :: LB)) (PL := PL) (EA := EA);
              [| | | | reflexivity | exact HArK | exact HArK | exact HArK | exact WRrP | exact NROr | exact NROr | exact NBr | exact NBr | exact HRC | exact INQ2 | exact AL8 | exact HPCP | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity].
            - eapply cenv_preA; [exact EVK | exact LSK | clear - LOK; lia | clear - KCOST CMM0; lia].
            - eapply cenv_roomA; [exact EVK | exact ROOM | clear; lia].
            - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EVK).
            - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_BN_mod_exp_recp_2ba604 CTX).
          }
          cbv beta. intros [us lss] Σs mss PO.
          apply (bn_postA_cpost ((q1, f + 32, 256) :: (q2, f + 352, 64) :: LB) PL EA lo (bv_unsigned sp) spa TOTAL Σ1 ls OW) in PO; [| exact OK | exact (proj1 (proj2 EVK))].
          cbn [fst snd] in *.
          destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & Fs & fcs & ms & OWs & PLs & -> & CPs & (EPLs & ->)).
          subst PLs. specialize (CPs eq_refl).
          destruct (cenv_postA ((q1, f + 32, 256) :: (q2, f + 352, 64) :: LB) PL EA lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls OW mb _ _ _ _ _ _ _ _ _ _ _ EVK CPs) as (EVs & LSs).
          pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CPs) as RSs. clear CPs.
          rewrite (ret_pc_even 2861036) by (clear; lia).
          unfold MallocRep.wz. apply implA_from_evt. step. if_false.
          step. rewrite unsigned_lit by (clear - CBN; lia). rewrite (bn_swrap32_small _) by (clear - CBN; lia).
          replace (Z.of_nat (S (S c)) + -1) with (Z.of_nat (S c)) by (clear; lia).
          step. if_cases KZ; rewrite ?unsigned_lit in KZ by (clear - CBN; lia); zify_cond KZ; try (exfalso; clear - KZ; lia).
          apply evt_done.
          eapply implA_mono; [eapply (IH mb pre (used + CMM)); [exact EVs| exact EPRE| exact LSs| exact (ref_at_stable _ _ _ _ PL _ _ RSs HArK)| clear - CBN; lia| clear - KCOST; lia]|].
          cbv beta. intros r Σ' ms' (mK' & OWK' & used' & R); unfold SQRQ. exists mK', OWK', used'.
          destruct R as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & E & K1 & K2 & K3 & K4).
          do 18 eexists. split; [exact E|]. split; [exact K1|]. split; [exact K2|]. split; [eapply refs_stable_trans; [exact RSs| exact K3]|]. clear - K4. lia.
      Qed.

      Lemma scan_loopA : forall c (i wvalue wend : Z) mb used ΣK lsK mK OWK (wstart window : Z) (POST : machine_state -> Prop)
          (x24 : word) (w0 w2 w3 w5 w7 w8 w9 : word)
          (x1 t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
        CENV mb (locs w0 (Z_to_bv 64 window) w2 w3 (Z_to_bv 64 wstart) w5 (Z_to_bv 64 wend) w7 w8 w9 ++ [CB g junk]) used ΣK lsK mK OWK ->
        lib_state lsK mK OWK PL EA -> ref_at lsK OWK PL rp arp ->
        1 <= i -> i + Z.of_nat c = window -> (0 < c)%nat -> window <= 6 -> 0 <= wstart < 2 ^ 31 -> 0 <= wend < i -> wend <= wstart -> 1 <= wvalue < 2 ^ (wend + 1) ->
        (forall mK' (wv' we' : Z) (x1' t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 x27 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32),
            CENV mb (locs w0 (Z_to_bv 64 window) w2 w3 (Z_to_bv 64 wstart) w5 (Z_to_bv 64 we') w7 w8 w9 ++ [CB g junk]) used ΣK lsK mK' OWK ->
            lib_state lsK mK' OWK PL EA ->
            window_scan (is_bit_set_pure (getbn rp lsK)) wstart c i wvalue wend = (wv', we') ->
            evt bgbsegs POST (bst x1' t0 t1 t2 a0 a1 (Z_to_bv 64 wv') a3 a4 a5 a6 a7 x24 (Z_to_bv 64 wstart) x27 t3 t4 t5 t6 F' 2860976 fc' mK')) ->
        evt bgbsegs POST (bst x1 t0 t1 t2 a0 a1 (Z_to_bv 64 wvalue) a3 a4 a5 a6 a7 x24 (Z_to_bv 64 wstart) (Z_to_bv 64 i) t3 t4 t5 t6 F 2860856 fc mK).
      Proof.
        induction c as [|c IH]; intros until fc; intros EVK LSK HApK I1 IC C0 W6 WS WE WES WV K; [lia|]. kit EVK. unfold bst, MallocRep.wz in *.
        assert (P2 : 2 ^ (wend + 1) <= 2 ^ i) by (apply Z.pow_le_mono_r; lia).
        assert (P6 : 2 ^ i <= 2 ^ 6) by (apply Z.pow_le_mono_r; lia).
        pose proof EVK as (_ & _ & STK & MIK & _ & _ & _ & _ & FRK & FSZK & _). cbn [app locs] in FRK.
        step. rewrite ?(unsigned_lit wstart), ?(unsigned_lit i) by (clear - WS I1 IC W6; lia).
        rewrite (bn_swrap32_small (wstart - i)) by (clear - WS I1 IC W6; lia).
        ub.
        step.
        step. rewrite lts_signed by (clear - WS I1 IC W6; lia).
        destruct (Z.ltb_spec (wstart - i) 0) as [LT|GE].
        -
          cbn [negb]. step. step.
          eapply (K mK wvalue wend); [exact EVK| exact LSK|]. cbn [window_scan]. replace (wstart - i <? 0) with true by (symmetry; apply Z.ltb_lt; exact LT). reflexivity.
        - cbn [negb].

          step. step.
    eapply (is_bit_set_callA ((q1, f + 32, 256) :: (q2, f + 352, 64) :: LB) PL EA lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls OW mb LOFB16); [exact EVK | exact LSK | exact HApK | exact NROp | clear - GE WS I1; lia |].
          intros mT y0T y1T y2T y4T y5T y6T y7T y8T y9T y10T y11T y12T y13T y14T EVT LST.
          rewrite (ret_pc_even 2860884) by (clear; lia).
      pose proof EVT as (_ & _ & STT & MIT & _ & _ & _ & _ & FRT & FSZT & _). cbn [app locs] in FRT.
          pose proof (munch_refl [(spa, spa + 88)]%Z mT) as MU. pose proof (wmono_refl bgbsegs mT) as WM.
          destruct (is_bit_set_pure (getbn rp lsK) (wstart - i)) eqn:EB; cbn [Z.b2z].
          +
            step. if_false.
            step.
            step. rewrite (unsigned_lit i), (unsigned_lit wend) by (clear - I1 WE IC W6; lia). rewrite (bn_swrap32_small (i - wend)) by (clear - I1 WE IC W6; lia).
            ub1 ub_kind. ub1 ub_kind. ub1 ub_kind. ub1 ub_kind.
            assert (WV25 : 0 <= wvalue < 2 ^ 25) by (clear - WV P2 P6; lia).
            rewrite ?(unsigned_lit wvalue) by (clear - WV25; lia).
            rewrite (ub_shl_ok wvalue (i - wend)) by (first [exact WV25 | clear - I1 WE IC W6; lia]).
            ub1 ub_kind.
            pose proof (lor_shiftl_1 wvalue (i - wend) ltac:(clear - WV P2; lia) ltac:(clear - WE; lia)) as LOR.
            assert (WB2 : 1 <= Z.lor (Z.shiftl wvalue (i - wend)) 1 < 2 ^ (i + 1)).
            { rewrite LOR.
              assert (2 <= 2 ^ (i - wend)) by (replace (2 ^ (i - wend)) with (2 * 2 ^ (i - wend - 1)) by (rewrite <- Z.pow_succ_r by (clear - WE; lia); f_equal; clear - WE; lia);
                                             assert (0 < 2 ^ (i - wend - 1)) by (apply Z.pow_pos_nonneg; clear - WE; lia); lia).
              assert (wvalue * 2 ^ (i - wend) <= (2 ^ (wend + 1) - 1) * 2 ^ (i - wend)) by (apply Z.mul_le_mono_nonneg_r; clear - WV WE H; lia).
              assert (2 ^ (wend + 1) * 2 ^ (i - wend) = 2 ^ (i + 1)) by (rewrite <- Z.pow_add_r by (clear - WE; lia); f_equal; clear - WE; lia).
              assert (0 <= wvalue * 2 ^ (i - wend)) by (apply Z.mul_nonneg_nonneg; clear - WV H; lia).
              assert ((2 ^ (wend + 1) - 1) * 2 ^ (i - wend) = 2 ^ (wend + 1) * 2 ^ (i - wend) - 2 ^ (i - wend)) by (clear; lia).
              clear - H H0 H1 H2 H3 WV. lia. }
            assert (P7 : 2 ^ (i + 1) <= 2 ^ 7) by (apply Z.pow_le_mono_r; clear - IC C0 W6; lia).
            assert (SH : 0 <= Z.shiftl wvalue (i - wend) < 2 ^ 7) by (rewrite LOR in WB2; rewrite Z.shiftl_mul_pow2 by (clear - WE; lia); clear - WB2 P7; lia).
            step. rewrite ?(unsigned_lit (i - wend)) by (clear - I1 WE IC W6; lia). rewrite ?(Z.mod_small (i - wend) 32) by (clear - I1 WE IC W6; lia).
            rewrite ?(unsigned_lit wvalue) by (clear - WV P2 P6; lia). rewrite ?(bn_swrap32_small (Z.shiftl wvalue (i - wend))) by (clear - SH; lia).
            step. rewrite ?(unsigned_lit (Z.shiftl wvalue (i - wend))) by (clear - SH; lia).
            step.
            lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mU end.
            relocal EVT LST MU WM STT MIT FRT FSZT EVU LSU. clear MU WM STT MIT FSZT.
            step.
            step. rewrite (swrap32_wrap64 i 1) by (clear - I1 IC W6; lia).
            step. step.
            step. if_cases KW; rewrite ?unsigned_lit in KW by (clear - I1 IC W6; lia); zify_cond KW.
            *
              eapply (IH (i + 1) (Z.lor (Z.shiftl wvalue (i - wend)) 1) i mb used ΣK lsK mU OWK wstart window POST x24 w0 w2 w3 w5 w7 w8 w9);
                [exact EVU| exact LSU| exact HApK| clear - I1; lia| clear - IC; lia| clear - IC KW; lia| exact W6| exact WS| clear - I1; lia| clear - GE; lia
                | exact WB2 |].
              intros mK' wv' we' x1' t0' t1' t2' a0' a1' a3' a4' a5' a6' a7' x27' t3' t4' t5' t6' F'' fc'' EV' LS' SC.
              eapply K; [exact EV'| exact LS'|]. cbn [window_scan]. replace (wstart - i <? 0) with false by (symmetry; apply Z.ltb_ge; exact GE). rewrite EB. exact SC.
            *
              step.
              eapply (K mU); [exact EVU| exact LSU|]. cbn [window_scan]. replace (wstart - i <? 0) with false by (symmetry; apply Z.ltb_ge; exact GE). rewrite EB.
              replace c with 0%nat by (clear - IC KW; lia). reflexivity.
          +
            step. if_true.
            step.
            step. rewrite (swrap32_wrap64 i 1) by (clear - I1 IC W6; lia).
            step. step.
            step. if_cases KW; rewrite ?unsigned_lit in KW by (clear - I1 IC W6; lia); zify_cond KW.
            * eapply (IH (i + 1) wvalue wend mb used ΣK lsK mT OWK wstart window POST x24 w0 w2 w3 w5 w7 w8 w9);
                [exact EVT| exact LST| exact HApK| clear - I1; lia| clear - IC; lia| clear - IC KW; lia| exact W6| exact WS| clear - WE; lia| exact WES| exact WV|].
              intros mK' wv' we' x1' t0' t1' t2' a0' a1' a3' a4' a5' a6' a7' x27' t3' t4' t5' t6' F'' fc'' EV' LS' SC.
              eapply K; [exact EV'| exact LS'|]. cbn [window_scan]. replace (wstart - i <? 0) with false by (symmetry; apply Z.ltb_ge; exact GE). rewrite EB. exact SC.
            * step.
              eapply (K mT); [exact EVT| exact LST|]. cbn [window_scan]. replace (wstart - i <? 0) with false by (symmetry; apply Z.ltb_ge; exact GE). rewrite EB.
              replace c with 0%nat by (clear - IC KW; lia). reflexivity.
      Qed.

      Definition vtab (lsK : bstate bptr) (OWK : list block) (ws : list word) (vals : list bnref) (addrs : list Z) : Prop :=
        length addrs = length vals /\
        forall i, (i < length vals)%nat ->
          nth_error ws i = Some (Z_to_bv 64 (nth i addrs 0)) /\ ref_at lsK OWK PL (nth i vals 0%nat) (nth i addrs 0)
          /\ (exists j, nth i vals 0%nat = RPool j) /\ 0 < nth i addrs 0 < 2^64.

      Lemma vtab_stable : forall lsK OWK ls' OW' ws vals addrs, vtab lsK OWK ws vals addrs -> refs_stable lsK OWK ls' OW' -> vtab ls' OW' ws vals addrs.
      Proof.
        intros lsK OWK ls' OW' ws vals addrs [L H] RS. split; [exact L|]. intros i Hi. destruct (H i Hi) as (H1 & H2 & H3 & H4).
        split; [exact H1|]. split; [exact (ref_at_stable _ _ _ _ PL _ _ RS H2)|]. split; [exact H3| exact H4].
      Qed.

      Lemma vtab_snoc : forall lsK OWK ws vals addrs v a j, vtab lsK OWK ws vals addrs -> (length vals < length ws)%nat ->
        ref_at lsK OWK PL v a -> v = RPool j -> 0 < a < 2^64 ->
        vtab lsK OWK (Arr.upd ws (length vals) (Z_to_bv 64 a)) (vals ++ [v]) (addrs ++ [a]).
      Proof.
        intros lsK OWK ws vals addrs v a j [L H] Hl HA Ev Ha. split; [rewrite !length_app; cbn; lia|].
        intros i Hi. rewrite length_app in Hi. cbn in Hi.
        destruct (Nat.lt_ge_cases i (length vals)) as [Hlt|Hge].
        - destruct (H i Hlt) as (H1 & H2 & H3 & H4). rewrite !app_nth1 by lia.
          split; [rewrite nth_error_upd_other by lia; exact H1|]. split; [exact H2|]. split; [exact H3| exact H4].
        - assert (Ei : i = length vals) by lia. subst i.
          rewrite app_nth2 by lia. rewrite (app_nth2 vals [v] 0%nat) by lia. rewrite L, Nat.sub_diag. cbn [nth].
          split; [apply nth_error_upd_same; exact Hl|]. split; [exact HA|]. split; [exists j; exact Ev| exact Ha].
      Qed.

      Local Notation ENDK := (fun p : unit * bstate bptr => tbind (BN_CTX_end (tree_ops bptr) (snd p)) (fun p' => BN_RECP_CTX_free (tree_ops bptr) (snd p'))).

      Definition WLOOP (fuel : nat) : Prop := forall (wstart : Z) (start : bool) mb used ΣK lsK mK OWK ws vals addrs (window : Z)
          (w0 w2 w4 w6 w8 w9 : word) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
        CENV mb (locs w0 (Z_to_bv 64 window) w2 (Z_to_bv 64 (Z.lxor (f + 32) 18446744073709551615)) w4 (Z_to_bv 64 (f + 32)) w6 (Z_to_bv 64 AN) w8 w9 ++ [CB g junk]) used ΣK lsK mK OWK ->
        lib_state lsK mK OWK PL EA -> ax_pres LB (bv_unsigned sp) (XW PL0) m1 mb ->
        u64arr bgbsegs mb (f + 32) ws -> length ws = 32%nat ->
        vtab lsK OWK ws vals addrs -> Z.of_nat (length vals) = (if 1 <? window then 2 ^ (window - 1) else 1) -> 1 <= window <= 6 ->
        0 <= wstart < Z.of_nat fuel -> wstart < 2 ^ 24 ->
        ref_at lsK OWK PL rr arr -> ref_at lsK OWK PL rp arp ->
        used + 2 * (wstart + 1) * CMM <= TOTAL ->
        implA (tbind (exp_window_loop (tree_ops bptr) MUL fuel rp rr vals window wstart start lsK) ENDK) ΣK Q
          (bst x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (Z.b2z (negb start))) (Z_to_bv 64 wstart) (Z_to_bv 64 (Z.b2z (negb start))) t3 t4 t5 t6 F 2860760 fc mK).

      Lemma after_scanA : forall fuel, WLOOP fuel -> forall (wstart wv we : Z) (start : bool) mb used ΣK lsK mK OWK ws vals addrs (window : Z)
          (w0 w2 w4 w6 w8 w9 : word) (x1 t0 t1 t2 a2 a3 a4 a5 a6 a7 x27 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
        CENV mb (locs w0 (Z_to_bv 64 window) w2 (Z_to_bv 64 (Z.lxor (f + 32) 18446744073709551615)) w4 (Z_to_bv 64 (f + 32)) w6 (Z_to_bv 64 AN) w8 w9 ++ [CB g junk]) used ΣK lsK mK OWK ->
        lib_state lsK mK OWK PL EA -> ax_pres LB (bv_unsigned sp) (XW PL0) m1 mb ->
        u64arr bgbsegs mb (f + 32) ws -> length ws = 32%nat ->
        vtab lsK OWK ws vals addrs -> Z.of_nat (length vals) = (if 1 <? window then 2 ^ (window - 1) else 1) -> 1 <= window <= 6 ->
        0 <= wstart < 2 ^ 24 -> 0 <= we < window -> we <= wstart -> 1 <= wv < 2 ^ (we + 1) -> wstart - (we + 1) < Z.of_nat fuel ->
        ref_at lsK OWK PL rr arr -> ref_at lsK OWK PL rp arp ->
        used + 2 * (wstart + 1) * CMM <= TOTAL ->
        implA (tbind (tbind ((if start then bret (tree_ops bptr) tt else exp_sqr_loop (tree_ops bptr) MUL (Z.to_nat (we + 1)) rr) lsK)
                            (fun p2 => tbind (BN_mod_mul_reciprocal (tree_ops bptr) rr rr (nth (Z.to_nat (Z.shiftr wv 1)) vals 0%nat) (snd p2))
                               (fun p => (if wstart - (we + 1) <? 0 then bret (tree_ops bptr) tt
                                          else exp_window_loop (tree_ops bptr) MUL fuel rp rr vals window (wstart - (we + 1)) false) (snd p)))) ENDK) ΣK Q
          (bst x1 t0 t1 t2 (Z_to_bv 64 we) (Z_to_bv 64 (Z.shiftr wv 1)) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (Z.b2z (negb start))) (Z_to_bv 64 wstart) x27 t3 t4 t5 t6 F 2860984 fc mK).
      Proof.
        intros fuel REC. intros until fc; intros EVK LSK AXB VB LEN VT VL WB WS WE WES WV WF HArK HApK KCOST. kitg EVK. unfold bst, MallocRep.wz in *.
        assert (L32 : Z.of_nat (length vals) <= 32).
        { rewrite VL. destruct (1 <? window); [|lia]. change 32 with (2 ^ 5). apply Z.pow_le_mono_r; lia. }
        assert (WV2 : 0 <= Z.shiftr wv 1 < Z.of_nat (length vals)).
        { rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2. rewrite VL.
          assert (2 ^ (we + 1) <= 2 ^ window) by (apply Z.pow_le_mono_r; lia).
          destruct (Z.ltb_spec 1 window) as [Hw|Hw].
          - assert (2 ^ window = 2 * 2 ^ (window - 1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia). split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia].
          - assert (we = 0) by lia. subst we. change (2 ^ (0 + 1)) with 2 in WV. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
        assert (WEC : 0 <= we * CMM) by (apply Z.mul_nonneg_nonneg; [clear - WE; lia | exact CMM0]).
        assert (WSC : 0 <= (wstart - we) * CMM) by (apply Z.mul_nonneg_nonneg; [clear - WES; lia | exact CMM0]).
        assert (NV : Z.lxor (f + 32) 18446744073709551615 = 18446744073709551615 - (f + 32)) by (apply W_gueron_arr.g_lxor_ones64; clear - G1 G3 C1 C2 C3; lia).

        assert (TAIL : forall used1 Σt ls1 mt OW1 (x1' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x24' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32),
              CENV mb (locs w0 (Z_to_bv 64 window) w2 (Z_to_bv 64 (Z.lxor (f + 32) 18446744073709551615)) w4 (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (Z.shiftr wv 1)) (Z_to_bv 64 AN) w8 w9 ++ [CB g junk]) used1 Σt ls1 mt OW1 ->
              lib_state ls1 mt OW1 PL EA -> refs_stable lsK OWK ls1 OW1 ->
              used1 + CMM + 2 * (wstart - we) * CMM <= TOTAL ->
              implA (tbind (BN_mod_mul_reciprocal (tree_ops bptr) rr rr (nth (Z.to_nat (Z.shiftr wv 1)) vals 0%nat) ls1)
                       (fun p => tbind ((if wstart - (we + 1) <? 0 then bret (tree_ops bptr) tt
                                         else exp_window_loop (tree_ops bptr) MUL fuel rp rr vals window (wstart - (we + 1)) false) (snd p)) ENDK)) Σt Q
                (MS (mkR x1' (Z_to_bv 64 spa) gp (Z_to_bv 64 TP_A) t0' t1' t2' sp (Z_to_bv 64 spa) a0' a1' a2' a3' a4' a5' a6' a7'
                         (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) (Z_to_bv 64 ac) (Z_to_bv 64 arr) (Z_to_bv 64 arp) (Z_to_bv 64 f) x24' (Z_to_bv 64 wstart) (Z_to_bv 64 SHB) (Z_to_bv 64 (we + 1)) t3' t4' t5' t6')
                    F' (Z_to_bv 64 2861048) fc' None mt (seg_rom bgbsegs))).
        { intros until fc'. intros EV1 LS1 RS1 KCOST1.
          pose proof VT as [VTL VT']. destruct (VT' (Z.to_nat (Z.shiftr wv 1)) ltac:(clear - WV2; lia)) as (Wi & HAi & (ji & Ei) & AiR). clear VT'.
          pose proof (ref_at_stable _ _ _ _ PL _ _ RS1 HArK) as HAr1.
      pose proof EV1 as (_ & _ & ST1 & MI1 & _ & _ & _ & _ & FR1 & FSZ1 & _). cbn [app locs] in FR1.
          pose proof (obj_arrA (q1, f + 32, 256) ((q2, f + 352, 64) :: LB) PL lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls OW mb _ _ _ _ _ _ ws EV1 VB
                        ltac:(cbn [blk_size snd]; rewrite LEN; reflexivity) ltac:(cbn [blk_addr blk_size fst snd]; intros xq Hxq; apply NFVP; clear - Hxq; lia)) as VA.
          cbn [blk_addr fst snd] in VA.
          pose proof (obj_acc _ _ _ _ (q1, f + 32, 256) (proj1 (proj2 EV1)) ltac:(left; reflexivity)) as ACCV. cbn [blk_addr blk_size fst snd] in ACCV.
          pose proof (munch_refl [] mt) as MU0.
          assert (XR : 0 <= f + 32 + Z.shiftr wv 1 * 8 < 2 ^ 64 /\ f + 32 <= f + 32 + Z.shiftr wv 1 * 8 /\ f + 32 + Z.shiftr wv 1 * 8 + 8 <= f + 32 + 256) by (clear - WV2 L32 G1 G3 C1 C2 C3; lia).
          apply implA_from_evt.

          ub1 ub_kind.
          step. rewrite ?(unsigned_lit (Z.shiftr wv 1)) by (clear - WV2 L32; lia).
          ub1 ub_kind.
          step. rewrite ?(unsigned_lit (Z.shiftr wv 1)) by (clear - WV2 L32; lia). rewrite Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 3) with 8.
          ub1 ub_kind. rewrite ?NV.
          ub1 ub_kind.
          step. step. rewrite ?(unsigned_lit (f + 32)) by (clear - XR WV2; lia). rewrite ?(unsigned_lit (Z.shiftr wv 1 * 8)) by (clear - WV2 L32; lia).
          step. rewrite ?(unsigned_lit (f + 32 + Z.shiftr wv 1 * 8)) by (clear - XR; lia).
          step. shl_with ACCV ALV. chk0.
          assert (Wi' : nth_error ws (Z.to_nat (Z.shiftr wv 1)) = Some (Z_to_bv 64 (nth (Z.to_nat (Z.shiftr wv 1)) addrs 0))) by exact Wi.
          let a := cur_mem_addr in pose proof (u64arr_read bgbsegs mt (f + 32) _ (Z.shiftr wv 1) _ a VA Wi' ltac:(clear - WV2; lia) ltac:(addr_tac)) as RD.
          step. clear RD VA Wi' ACCV MU0.

          step. step. step. step. step.
    apply evt_done.
          eapply implA_bind.
          { eapply (BN_mod_mul_reciprocal_walkA) with (lo := lo) (OW := OW1) (LB := ((q1, f + 32, 256) :: (q2, f + 352, 64) :: LB)) (PL := PL) (EA := EA);
              [| | | | reflexivity | exact HAr1 | exact HAr1 | exact (ref_at_stable _ _ _ _ PL _ _ RS1 HAi) | exact WRrP | exact NROr | rewrite Ei; unfold RPool, ROne, NFIX; clear; lia | exact NBr | rewrite Ei; apply nbuf_pool | exact HRC | exact INQ2 | exact AL8 | exact HPCP | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity].
            - eapply cenv_preA; [exact EV1 | exact LS1 | clear - LOK; lia | clear - KCOST1 CMM0 WSC; lia].
            - eapply cenv_roomA; [exact EV1 | exact ROOM | clear; lia].
            - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EV1).
            - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_BN_mod_exp_recp_2ba658 CTX).
          }
          cbv beta. intros [uv lsv] Σv msv PO.
          apply (bn_postA_cpost ((q1, f + 32, 256) :: (q2, f + 352, 64) :: LB) PL EA lo (bv_unsigned sp) spa TOTAL Σ1 ls OW) in PO; [| exact OK | exact (proj1 (proj2 EV1))].
          cbn [fst snd] in *.
          destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & Fv & fcv & mv & OWv & PLv & -> & CPv & (EPLv & ->)).
          subst PLv. specialize (CPv eq_refl).
          destruct (cenv_postA ((q1, f + 32, 256) :: (q2, f + 352, 64) :: LB) PL EA lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls OW mb _ _ _ _ _ _ _ _ _ _ _ EV1 CPv) as (EVv & LSv).
          pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CPv) as RSv. clear CPv.
          rewrite (ret_pc_even 2861120) by (clear; lia).
          pose proof (refs_stable_trans _ _ _ _ _ _ RS1 RSv) as RS0v.
          unfold MallocRep.wz. apply implA_from_evt. step. if_false.
      pose proof EVv as (_ & _ & STv & MIv & _ & _ & _ & _ & FRv & FSZv & _). cbn [app locs] in FRv.

          step. step. rewrite ?(unsigned_lit wstart) by (clear - WS; lia). rewrite ?(unsigned_lit (we + 1)) by (clear - WE WB; lia).
          rewrite ?(bn_swrap32_small (wstart - (we + 1))) by (clear - WS WE WB; lia).
          ub1 ub_kind.
          step. rewrite (swrap32_of_u64 (wstart + - (we + 1))) by (clear - WS WE WB; lia). replace (wstart + - (we + 1)) with (wstart - (we + 1)) by (clear; lia).
          step. step.
          step. rewrite lts_signed by (clear - WS WE WB; lia).
          destruct (Z.ltb_spec (wstart - (we + 1)) 0) as [WLT|WGE]; cbn [negb].
          -
            step.
            apply evt_done. unfold bret. cbn [ret tree_ops tbind fst snd].
            eapply exit_tail; [exact EVv | reflexivity | exact LSv | clear - KCOST1 CMM0 WSC; lia | exact AXB].
          -
            step.
            apply evt_done.
            eapply (REC (wstart - (we + 1)) false mb _ _ _ mv _ ws vals addrs window);
              [exact EVv| exact LSv| exact AXB| exact VB| exact LEN| eapply vtab_stable; [exact VT| exact RS0v]| exact VL| exact WB| clear - WGE WF; lia| clear - WS WE; lia
              | exact (ref_at_stable _ _ _ _ PL _ _ RS0v HArK)| exact (ref_at_stable _ _ _ _ PL _ _ RS0v HApK)
              | clear - KCOST1; lia]. }
        apply implA_tbind_assoc.
      pose proof EVK as (_ & _ & STK & MIK & _ & _ & _ & _ & FRK & FSZK & _). cbn [app locs] in FRK.
        pose proof (munch_refl [(spa, spa + 88)]%Z mK) as MU. pose proof (wmono_refl bgbsegs mK) as WM.
        destruct start; cbn [negb Z.b2z] in *.
        -
          rewrite tbind_bret. cbv beta. cbn [fst snd].
          apply implA_from_evt.
          step.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mS end.
          relocal EVK LSK MU WM STK MIK FRK FSZK EVS LSS. clear MU WM STK MIK FSZK.
          step. rewrite ?(unsigned_lit we) by (clear - WE WB; lia). rewrite ?(swrap32_wrap64 we 1) by (clear - WE WB; lia). rewrite ?(bn_swrap32_small (we + 1)) by (clear - WE WB; lia).
          ub1 ub_kind.
          step. try unfold v_slt, c_lts. rewrite ?lts_signed by (clear - WE WB; lia). replace (0 <? we + 1) with true by (symmetry; apply Z.ltb_lt; clear - WE; lia).
          step. step.
          step. if_true.
          apply evt_done. apply implA_tbind_assoc. eapply TAIL; [exact EVS| exact LSS| apply refs_stable_refl| clear - KCOST CMM0 WEC; lia].
        -
          apply implA_from_evt.
          step.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mS end.
          relocal EVK LSK MU WM STK MIK FRK FSZK EVS LSS. clear MU WM STK MIK FSZK.
          step. rewrite ?(unsigned_lit we) by (clear - WE WB; lia). rewrite ?(swrap32_wrap64 we 1) by (clear - WE WB; lia). rewrite ?(bn_swrap32_small (we + 1)) by (clear - WE WB; lia).
          ub1 ub_kind.
          step. try unfold v_slt, c_lts. rewrite ?lts_signed by (clear - WE WB; lia). replace (0 <? we + 1) with true by (symmetry; apply Z.ltb_lt; clear - WE; lia).
          step. step.
          step. if_false.
          replace (Z.to_nat (we + 1)) with (S (Z.to_nat we)) by (clear - WE; lia).
          assert (EWE : Z_to_bv 64 (we + 1) = Z_to_bv 64 (Z.of_nat (S (Z.to_nat we)))) by (f_equal; clear - WE; lia).
          rewrite EWE.
          apply evt_done. eapply implA_bind.
          { eapply (sqr_loopA (Z.to_nat we) mb _ used); [exact EVS| reflexivity| exact LSS| exact HArK| clear - WE WB; lia
              | replace (Z.of_nat (S (Z.to_nat we))) with (we + 1) by (clear - WE; lia); clear - KCOST CMM0 WEC WSC; lia]. }
          cbv beta. intros [uq lsq] Σq msq (mq & OWq & usedq & R).
          destruct R as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & -> & EVq & LSq & RSq & UQ). cbn [fst snd] in *.
          replace (Z.of_nat (S (Z.to_nat we))) with (we + 1) in UQ by (clear - WE; lia).
          unfold bst. rewrite <- EWE. apply implA_tbind_assoc. eapply TAIL; [exact EVq| exact LSq| exact RSq| clear - KCOST UQ CMM0 WEC; lia].
      Qed.

      Lemma window_loopA : forall fuel, WLOOP fuel.
      Proof.
        induction fuel as [|fuel IH]; unfold WLOOP; intros until fc; intros EVK LSK AXB VB LEN VT VL WB WS WS24 HArK HApK KCOST; [exfalso; clear - WS; lia|].
        kitg EVK. unfold bst, MallocRep.wz in *.
        assert (WSC : 0 <= wstart * CMM) by (apply Z.mul_nonneg_nonneg; [clear - WS; lia | exact CMM0]).
        apply implA_from_evt.

        step. step. step.
    eapply (is_bit_set_callA ((q1, f + 32, 256) :: (q2, f + 352, 64) :: LB) PL EA lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls OW mb LOFB16); [exact EVK | exact LSK | exact HApK | exact NROp | clear - WS WS24; lia |].
        intros mi y0i y1i y2i y4i y5i y6i y7i y8i y9i y10i y11i y12i y13i y14i EVi LSi.
        rewrite (ret_pc_even 2860772) by (clear; lia).
      pose proof EVi as (_ & _ & STi & MIi & _ & _ & _ & _ & FRi & FSZi & _). cbn [app locs] in FRi.
        pose proof (munch_refl [(spa, spa + 88)]%Z mi) as MU. pose proof (wmono_refl bgbsegs mi) as WM.
        destruct (is_bit_set_pure (getbn rp lsK) wstart) eqn:EB; cbn [Z.b2z].
        -
          destruct (window_scan (is_bit_set_pure (getbn rp lsK)) wstart (Z.to_nat (window - 1)) 1 1 0) as [wv we] eqn:SC.
          rewrite (ewl_set MUL fuel rp rr vals window wstart start lsK wv we EB SC). cbv beta.
          pose proof (window_scan_bnd (is_bit_set_pure (getbn rp lsK)) wstart (Z.to_nat (window - 1)) 1 1 0
                        ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - WS; lia) ltac:(clear; cbn; lia)) as BND.
          rewrite SC in BND. destruct BND as (WE & WES & WV).
          replace (1 + Z.of_nat (Z.to_nat (window - 1))) with window in WE by (clear - WB; lia).
          step. if_true. step. step.
          step. rewrite lts_signed by (clear - WB; lia).
          destruct (Z.ltb_spec window 2) as [KW|KW].
          +
            assert (W1 : window = 1) by (clear - KW WB; lia). subst window.
            change (Z.to_nat (1 - 1)) with 0%nat in SC. cbn [window_scan] in SC. injection SC as <- <-.
            step. step. step.
            apply evt_done.
            eapply (after_scanA fuel IH wstart 1 0 start mb used _ lsK mi OWK ws vals addrs 1);
              [exact EVi| exact LSi| exact AXB| exact VB| exact LEN| exact VT| exact VL| exact WB| clear - WS WS24; lia| clear; lia| clear - WS; lia| clear; cbn; lia| clear - WS; lia
              | exact HArK| exact HApK| exact KCOST].
          +
            lstep 0. step. step. step.
            lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mA end.
            relocal EVi LSi MU WM STi MIi FRi FSZi EVa LSa. clear MU WM STi MIi FRi FSZi.
            eapply (scan_loopA (Z.to_nat (window - 1)) 1 1 0 mb used _ lsK mA OWK wstart window);
              [exact EVa| exact LSa| exact HApK| clear; lia| clear - WB; lia| clear - KW WB; lia| clear - WB; lia| clear - WS WS24; lia| clear; lia| clear - WS; lia
              | clear; cbn; lia|].
            intros mK' wv' we' x1' t0' t1' t2' a0' a1' a3' a4' a5' a6' a7' x27' t3' t4' t5' t6' F' fc' EV' LS' SC'.
            rewrite SC in SC'. injection SC' as <- <-.
            assert (P7 : 2 ^ (we + 1) <= 2 ^ 7) by (apply Z.pow_le_mono_r; clear - WE WB; lia).
            assert (SHR : 0 <= Z.shiftr wv 1 < 2 ^ 7) by (rewrite Z.shiftr_div_pow2 by (clear; lia); change (2 ^ 1) with 2; clear - WV P7; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
            unfold bst.
      pose proof EV' as (_ & _ & STx & MIx & _ & _ & _ & _ & FRx & FSZx & _). cbn [app locs] in FRx.
            step. rewrite ?(unsigned_lit wv) by (clear - WV P7; lia). rewrite ?(bn_swrap32_small wv) by (clear - WV P7; lia).
            rewrite ?(bn_swrap32_small (Z.shiftr wv 1)) by (clear - SHR; lia).
            step.
            apply evt_done.
            eapply (after_scanA fuel IH wstart wv we start mb used _ lsK mK' OWK ws vals addrs window);
              [exact EV'| exact LS'| exact AXB| exact VB| exact LEN| exact VT| exact VL| exact WB| clear - WS WS24; lia| exact WE| exact WES| exact WV| clear - WS WE; lia
              | exact HArK| exact HApK| exact KCOST].
        -
          rewrite (ewl_clear MUL fuel rp rr vals window wstart start lsK EB). cbv beta.
          step. if_false.
          assert (NEXT : forall used1 Σn ls1 mn OW1 (x1' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32),
                CENV mb (locs w0 (Z_to_bv 64 window) w2 (Z_to_bv 64 (Z.lxor (f + 32) 18446744073709551615)) w4 (Z_to_bv 64 (f + 32)) w6 (Z_to_bv 64 AN) w8 w9 ++ [CB g junk]) used1 Σn ls1 mn OW1 ->
                lib_state ls1 mn OW1 PL EA -> refs_stable lsK OWK ls1 OW1 -> used1 + 2 * wstart * CMM <= TOTAL ->
                implA (tbind ((if wstart =? 0 then bret (tree_ops bptr) tt
                               else exp_window_loop (tree_ops bptr) MUL fuel rp rr vals window (wstart - 1) start) ls1) ENDK) Σn Q
                  (MS (mkR x1' (Z_to_bv 64 spa) gp (Z_to_bv 64 TP_A) t0' t1' t2' sp (Z_to_bv 64 spa) a0' a1' a2' a3' a4' a5' a6' a7'
                         (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) (Z_to_bv 64 ac) (Z_to_bv 64 arr) (Z_to_bv 64 arp) (Z_to_bv 64 f) (Z_to_bv 64 (Z.b2z (negb start))) (Z_to_bv 64 wstart) (Z_to_bv 64 SHB) (Z_to_bv 64 (Z.b2z (negb start))) t3' t4' t5' t6')
                    F' (Z_to_bv 64 2860808) fc' None mn (seg_rom bgbsegs))).
          { intros until fc'. intros EV1 LS1 RS1 KCOST1.
      pose proof EV1 as (_ & _ & ST1 & MI1 & _ & _ & _ & _ & FR1 & FSZ1 & _). cbn [app locs] in FR1.
            apply implA_from_evt.
            destruct (Z.eqb_spec wstart 0) as [W0|WN0].
            -
              subst wstart.
              step. if_true. step. step. step. step.
              apply evt_done. unfold bret. cbn [ret tree_ops tbind fst snd].
              eapply exit_tail; [exact EV1 | reflexivity | exact LS1 | clear - KCOST1; lia | exact AXB].
            - step. if_cases KZ; rewrite ?unsigned_lit in KZ by (clear - WS WS24; lia); zify_cond KZ; [exfalso; clear - KZ WN0; lia|].
              step. rewrite (swrap32_wrap64 wstart (-1)) by (clear - WS WS24; lia). replace (wstart + -1) with (wstart - 1) by (clear; lia).
              ub1 ub_kind.
              step. step.
              apply evt_done.
              eapply (IH (wstart - 1) start mb _ _ _ mn _ ws vals addrs window);
                [exact EV1| exact LS1| exact AXB| exact VB| exact LEN| eapply vtab_stable; [exact VT| exact RS1]| exact VL| exact WB| clear - WS WN0; lia| clear - WS24; lia
                | exact (ref_at_stable _ _ _ _ PL _ _ RS1 HArK)| exact (ref_at_stable _ _ _ _ PL _ _ RS1 HApK)
                | clear - KCOST1; lia]. }
          apply evt_done. apply implA_tbind_assoc.
          destruct start; cbn [negb Z.b2z] in *.
          +
            rewrite tbind_bret. cbv beta. cbn [fst snd].
            apply implA_from_evt. step. if_true.
            apply evt_done. eapply NEXT; [exact EVi| exact LSi| apply refs_stable_refl| clear - KCOST CMM0 WSC; lia].
          +
            apply implA_from_evt. step. if_false.
            do 5 step. step.
    apply evt_done.
            eapply implA_bind.
            { eapply (BN_mod_mul_reciprocal_walkA) with (lo := lo) (OW := OWK) (LB := ((q1, f + 32, 256) :: (q2, f + 352, 64) :: LB)) (PL := PL) (EA := EA);
                [| | | | reflexivity | exact HArK | exact HArK | exact HArK | exact WRrP | exact NROr | exact NROr | exact NBr | exact NBr | exact HRC | exact INQ2 | exact AL8 | exact HPCP | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity].
              - eapply cenv_preA; [exact EVi | exact LSi | clear - LOK; lia | clear - KCOST CMM0 WSC; lia].
              - eapply cenv_roomA; [exact EVi | exact ROOM | clear; lia].
              - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EVi).
              - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_BN_mod_exp_recp_2ba51c CTX).
            }
            cbv beta. intros [ur lsr] Σr msr PO.
            apply (bn_postA_cpost ((q1, f + 32, 256) :: (q2, f + 352, 64) :: LB) PL EA lo (bv_unsigned sp) spa TOTAL Σ1 ls OW) in PO; [| exact OK | exact (proj1 (proj2 EVi))].
            cbn [fst snd] in *.
            destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & Fr & fcr & mr & OWr & PLr & -> & CPr & (EPLr & ->)).
            subst PLr. specialize (CPr eq_refl).
            destruct (cenv_postA ((q1, f + 32, 256) :: (q2, f + 352, 64) :: LB) PL EA lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls OW mb _ _ _ _ _ _ _ _ _ _ _ EVi CPr) as (EVr & LSr).
            pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CPr) as RSr. clear CPr.
            rewrite (ret_pc_even 2860804) by (clear; lia).
            unfold MallocRep.wz. apply implA_from_evt. step. if_false.
            apply evt_done. eapply NEXT; [exact EVr| exact LSr| exact RSr| clear - KCOST CMM0; lia].
      Qed.

      Lemma win_entryA : forall fuel (wstart : Z) (start : bool) mb used ΣK lsK mK OWK ws vals addrs (window : Z)
          (w0 w2 w4 w6 w8 w9 : word) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x27 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
        CENV mb (locs w0 (Z_to_bv 64 window) w2 (Z_to_bv 64 (Z.lxor (f + 32) 18446744073709551615)) w4 (Z_to_bv 64 (f + 32)) w6 (Z_to_bv 64 AN) w8 w9 ++ [CB g junk]) used ΣK lsK mK OWK ->
        lib_state lsK mK OWK PL EA -> ax_pres LB (bv_unsigned sp) (XW PL0) m1 mb ->
        u64arr bgbsegs mb (f + 32) ws -> length ws = 32%nat ->
        vtab lsK OWK ws vals addrs -> Z.of_nat (length vals) = (if 1 <? window then 2 ^ (window - 1) else 1) -> 1 <= window <= 6 ->
        0 <= wstart < Z.of_nat fuel -> wstart < 2 ^ 24 ->
        ref_at lsK OWK PL rr arr -> ref_at lsK OWK PL rp arp ->
        used + 2 * (wstart + 1) * CMM <= TOTAL ->
        implA (tbind (exp_window_loop (tree_ops bptr) MUL fuel rp rr vals window wstart start lsK) ENDK) ΣK Q
          (bst x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (Z.b2z (negb start))) (Z_to_bv 64 wstart) x27 t3 t4 t5 t6 F 2860756 fc mK).
      Proof.
        intros until fc; intros EVK LSK AXB VB LEN VT VL WB WS WS24 HArK HApK KCOST. kit EVK. unfold bst, MallocRep.wz in *.
        apply implA_from_evt.
        step. rewrite ?(unsigned_lit (Z.b2z (negb start))) by (clear; destruct start; cbn; lia).
        replace (Z.land (Z.b2z (negb start)) 1) with (Z.b2z (negb start)) by (clear; destruct start; reflexivity).
        apply evt_done.
        eapply (window_loopA fuel wstart start mb used _ lsK mK OWK ws vals addrs window);
          [exact EVK| exact LSK| exact AXB| exact VB| exact LEN| exact VT| exact VL| exact WB| exact WS| exact WS24| exact HArK| exact HApK| exact KCOST].
      Qed.

      Definition restm (bits window : Z) (vals : list bnref) (s : bstate bptr) : btree bptr (unit * bstate bptr) :=
        (if (rr =? rp)%nat then (fun _ : bstate bptr => TUnr)
         else fun s12 : bstate bptr => tbind (BN_one (tree_ops bptr) rr s12)
                (fun p0 : unit * bstate bptr => exp_window_loop (tree_ops bptr) MUL (Z.to_nat bits) rp rr vals window (bits - 1) true (snd p0))) s.

      Lemma L_restA : forall mb used ΣK lsK mK OWK ws vals addrs (bits window : Z)
          (w0 w2 w3 w4 w6 w8 w9 : word) (x1 t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 x24 x25 x27 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
        CENV mb (locs w0 (Z_to_bv 64 window) w2 w3 w4 (Z_to_bv 64 (f + 32)) w6 (Z_to_bv 64 AN) w8 w9 ++ [CB g junk]) used ΣK lsK mK OWK ->
        lib_state lsK mK OWK PL EA -> ax_pres LB (bv_unsigned sp) (XW PL0) m1 mb ->
        u64arr bgbsegs mb (f + 32) ws -> length ws = 32%nat ->
        vtab lsK OWK ws vals addrs -> Z.of_nat (length vals) = (if 1 <? window then 2 ^ (window - 1) else 1) -> 1 <= window <= 6 ->
        0 < bits <= 32768 ->
        used + MC + 2 * bits * CMM <= TOTAL ->
        implA (tbind (restm bits window vals lsK) ENDK) ΣK Q
          (bst x1 t0 t1 t2 a0 (Z_to_bv 64 bits) a2 a3 a4 a5 a6 a7 x24 x25 x27 t3 t4 t5 t6 F 2860708 fc mK).
      Proof.
        intros until fc; intros EVK LSK AXB VB LEN VT VL WB BITS KCOST. kitg EVK. unfold bst, restm, MallocRep.wz in *.
        pose proof EVK as (_ & HEAPK & _ & _ & _ & _ & _ & RSK & _).
        pose proof (AH_nodup_l _ _ _ _ HEAPK) as NDK. pose proof (lib_state_h_parts _ _ _ _ _ _ LSK) as PARTSK.
        pose proof (ref_at_stable _ _ _ _ PL _ _ RSK HArP) as HArK. pose proof (ref_at_stable _ _ _ _ PL _ _ RSK HApP) as HApK.
        assert (ArR : 0 < arr < 2^64) by (pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAPK PARTSK FROKK HArK NROr) as (X & Y & _); unfold BnHeapA.ACEIL in *; clear - X Y C1 C2 C3; lia).
        assert (ApR : 0 < arp < 2^64) by (pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAPK PARTSK FROKK HApK NROp) as (X & Y & _); unfold BnHeapA.ACEIL in *; clear - X Y C1 C2 C3; lia).
        assert (BC : 0 <= bits * CMM) by (apply Z.mul_nonneg_nonneg; [clear - BITS; lia | exact CMM0]).
      pose proof EVK as (_ & _ & STK & MIK & _ & _ & _ & _ & FRK & FSZK & _). cbn [app locs] in FRK.
        apply implA_from_evt.

        step. rewrite ?(unsigned_lit bits) by (clear - BITS; lia). rewrite ?(swrap32_wrap64 bits (-1)) by (clear - BITS; lia). rewrite ?(bn_swrap32_small (bits + -1)) by (clear - BITS; lia).
        ub1 ub_kind.
        step. if_cases KE; rewrite ?unsigned_lit in KE by (clear - ArR ApR; lia); zify_cond KE.
        {
          assert (Erp : rr = rp).
          { destruct (Nat.eq_dec rr rp) as [E|NE]; [exact E| exfalso].
            pose proof (struct_disj ΣK OWK LBX mK HEAPK lsK PL EA _ _ PARTSK FROKK rr rp arr arp NE HArK HApK) as D. clear - D KE. lia. }
          replace ((rr =? rp)%nat) with true by (symmetry; apply Nat.eqb_eq; exact Erp).
          apply evt_done. cbn [tbind]. apply implA_unr. }
        assert (NErp : rr <> rp) by (intros E; rewrite <- E in HApK; pose proof (ref_at_fun _ _ _ _ _ _ NDK HArK HApK) as EA_; clear - EA_ KE; lia).
        replace ((rr =? rp)%nat) with false by (symmetry; apply Nat.eqb_neq; exact NErp).

        step. step. step. step.
        unfold BN_one.
    apply evt_done.
        apply implA_tbind_assoc. eapply implA_bind.
        { eapply (BN_set_word_walkA) with (lo := lo) (OW := OWK) (LB := ((q1, f + 32, 256) :: (q2, f + 352, 64) :: LB)) (PL := PL) (EA := EA) (w := 1);
            [| | | reflexivity | exact HArK | exact (hpl_wref _ _ WRrP) | reflexivity | reflexivity | clear; lia].
          - eapply cenv_preA; [exact EVK | exact LSK | clear - LOK CSsetw; lia | clear - KCOST MCP CMM0 BC; lia].
          - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EVK).
          - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_BN_mod_exp_recp_2ba4d8 CTX).
        }
        cbv beta. intros [uo lso] Σo mso PO.
        apply (bn_postA_cpost ((q1, f + 32, 256) :: (q2, f + 352, 64) :: LB) PL EA lo (bv_unsigned sp) spa TOTAL Σ1 ls OW) in PO; [| exact OK | exact (proj1 (proj2 EVK))].
        cbn [fst snd] in *.
        destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & Fo & fco & mo & OWo & PLo & -> & CPo & (EPLo & -> & INCLo)).
        subst PLo. specialize (CPo eq_refl).
        destruct (cenv_postA ((q1, f + 32, 256) :: (q2, f + 352, 64) :: LB) PL EA lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls OW mb _ _ _ _ _ _ _ _ _ _ _ EVK CPo) as (EVo & LSo).
        pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CPo) as RSo. clear CPo.
        rewrite (ret_pc_even 2860736) by (clear; lia).
        unfold MallocRep.wz. apply implA_from_evt. step. if_false.

      pose proof EVo as (_ & _ & STo & MIo & _ & _ & _ & _ & FRo & FSZo & _). cbn [app locs] in FRo.
        pose proof (munch_refl [(spa, spa + 88)]%Z mo) as MU. pose proof (wmono_refl bgbsegs mo) as WM.
        step. step.
        step. rewrite ?(unsigned_lit (f + 32)) by (clear - G1 G3 C1 C2 C3; lia).
        step.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mE end.
        relocal EVo LSo MU WM STo MIo FRo FSZo EVe LSe. clear MU WM STo MIo FSZo.
        replace (bits + -1) with (bits - 1) by (clear; lia).
        apply evt_done.
        eapply (win_entryA (Z.to_nat bits) (bits - 1) true mb _ _ _ mE _ ws vals addrs window);
          [exact EVe| exact LSe| exact AXB| exact VB| exact LEN| eapply vtab_stable; [exact VT| exact RSo]| exact VL| exact WB| clear - BITS; lia| clear - BITS; lia
          | exact (ref_at_stable _ _ _ _ PL _ _ RSo HArK)| exact (ref_at_stable _ _ _ _ PL _ _ RSo HApK)
          | replace (bits - 1 + 1) with bits by (clear; lia); clear - KCOST; lia].
      Qed.

      Lemma table_bodyA : forall vals addrs mb used ΣK lsK mK OWK ws (bits window : Z) (d : bnref) (ad : Z) (di : nat)
          (K : bnref -> bstate bptr -> btree bptr (list bnref * bstate bptr)) (G : list bnref * bstate bptr -> btree bptr (unit * bstate bptr))
          (w0 w3 w8 w9 : word) (x1 t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
        CENV mb (locs w0 (Z_to_bv 64 window) (Z_to_bv 64 (window - 1)) w3 (Z_to_bv 64 bits) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 ad) (Z_to_bv 64 AN) w8 w9 ++ [CB g junk]) used ΣK lsK mK OWK ->
        lib_state lsK mK OWK PL EA -> ax_pres LB (bv_unsigned sp) (XW PL0) m1 mb ->
        u64arr bgbsegs mb (f + 32) ws -> length ws = 32%nat ->
        vtab lsK OWK ws vals addrs -> (1 <= length vals)%nat -> (length vals < 32)%nat -> 1 < window <= 6 ->
        ref_at lsK OWK PL d ad -> d = RPool di ->
        used + MC + CMM <= TOTAL ->
        (forall v av mb2 Σ2 ls2 m2 OW2 ws2 (x1' t0' t1' t2' a0' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32),
            CENV mb2 (locs w0 (Z_to_bv 64 window) (Z_to_bv 64 (window - 1)) (Z_to_bv 64 (Z.of_nat (length vals) + 1)) (Z_to_bv 64 bits) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 ad) (Z_to_bv 64 AN) w8 w9 ++ [CB g junk]) (used + MC + CMM) Σ2 ls2 m2 OW2 ->
            lib_state ls2 m2 OW2 PL EA -> ax_pres LB (bv_unsigned sp) (XW PL0) m1 mb2 ->
            u64arr bgbsegs mb2 (f + 32) ws2 -> length ws2 = 32%nat ->
            vtab ls2 OW2 ws2 (vals ++ [v]) (addrs ++ [av]) -> ref_at ls2 OW2 PL d ad -> refs_stable lsK OWK ls2 OW2 ->
            implA (tbind (K v ls2) G) Σ2 Q
              (MS (mkR x1' (Z_to_bv 64 spa) gp (Z_to_bv 64 TP_A) t0' t1' t2' sp (Z_to_bv 64 spa) a0' (Z_to_bv 64 (Z.of_nat (length vals) + 1)) a2' a3' a4' a5' a6' a7'
                         (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) (Z_to_bv 64 ac) (Z_to_bv 64 arr) (Z_to_bv 64 arp) (Z_to_bv 64 f) (Z_to_bv 64 (f + 32 + 8 * Z.of_nat (length vals))) (Z_to_bv 64 (f + 32 + 8 * Z.of_nat (length vals))) (Z_to_bv 64 SHB) (Z_to_bv 64 (32 - Z.of_nat (length vals))) t3' t4' t5' t6')
                    F' (Z_to_bv 64 2860664) fc' None m2 (seg_rom bgbsegs))) ->
        implA (tbind (BN_CTX_get (tree_ops bptr) lsK)
                     (fun p => tbind (tbind (BN_mod_mul_reciprocal (tree_ops bptr) (fst p) (last vals 0%nat) d (snd p)) (fun p0 => K (fst p) (snd p0))) G)) ΣK Q
          (MS (mkR x1 (Z_to_bv 64 spa) gp (Z_to_bv 64 TP_A) t0 t1 t2 sp (Z_to_bv 64 spa) a0 (Z_to_bv 64 (Z.of_nat (length vals) + 1)) a2 a3 a4 a5 a6 a7
                         (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) (Z_to_bv 64 ac) (Z_to_bv 64 arr) (Z_to_bv 64 arp) (Z_to_bv 64 f) (Z_to_bv 64 (f + 32 + 8 * Z.of_nat (length vals))) (Z_to_bv 64 (f + 32 + 8 * Z.of_nat (length vals))) (Z_to_bv 64 SHB) (Z_to_bv 64 (32 - Z.of_nat (length vals))) t3 t4 t5 t6)
                    F (Z_to_bv 64 2860596) fc None mK (seg_rom bgbsegs)).
      Proof.
        intros until fc; intros EVK LSK AXB VB LEN VT K1 K32 WB HAd Ed KCOST CONT2. kitg EVK. unfold MallocRep.wz in *.
        assert (NROd : d <> ROne) by (rewrite Ed; unfold RPool, ROne, NFIX; clear; lia).

      pose proof EVK as (_ & _ & STK & MIK & _ & _ & _ & _ & FRK & FSZK & _). cbn [app locs] in FRK.
        pose proof (munch_refl [(spa, spa + 88)]%Z mK) as MU. pose proof (wmono_refl bgbsegs mK) as WM.
        apply implA_from_evt. step.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mS end.
        relocal EVK LSK MU WM STK MIK FRK FSZK EVS LSS. clear MU WM STK MIK FSZK FRK.

        step. step.
    apply evt_done.
        eapply implA_bind.
        { eapply (BN_CTX_get_walkA) with (lo := lo) (OW := OWK) (LB := ((q1, f + 32, 256) :: (q2, f + 352, 64) :: LB)) (PL := PL) (EA := EA);
            [| | | reflexivity | exact HPCP | reflexivity].
          - eapply cenv_preA; [exact EVS | exact LSS | clear - LOK CSget; lia | clear - KCOST CMM0; lia].
          - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EVS).
          - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_BN_mod_exp_recp_2ba458 CTX).
        }
        cbv beta. intros [ug lsg] Σg msg PO.
        apply (bn_postA_cpost ((q1, f + 32, 256) :: (q2, f + 352, 64) :: LB) PL EA lo (bv_unsigned sp) spa TOTAL Σ1 ls OW) in PO; [| exact OK | exact (proj1 (proj2 EVS))].
        cbn [fst snd] in *.
        destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & Fg & fcg & mg & OWg & PLg & -> & CPg & (EPLg & (vi & Ev) & (av & HAv & ->) & INCLg)).
        subst PLg. specialize (CPg eq_refl).
        destruct (cenv_postA ((q1, f + 32, 256) :: (q2, f + 352, 64) :: LB) PL EA lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls OW mb _ _ _ _ _ _ _ _ _ _ _ EVS CPg) as (EVg & LSg).
        pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CPg) as RSg. clear CPg.
        rewrite (ret_pc_even 2860608) by (clear; lia).
        pose proof (proj1 (proj2 EVg)) as HEAPg. pose proof (lib_state_h_parts _ _ _ _ _ _ LSg) as PARTSg.
        assert (NROv : ug <> ROne) by (rewrite Ev; unfold RPool, ROne, NFIX; clear; lia).
        pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAPg PARTSg FROKK HAv NROv) as (Av0 & AvC & _).
        assert (AvR : 0 < av < 2^64) by (unfold BnHeapA.ACEIL, STACK_WIN in *; clear - Av0 AvC C1 C2 C3; lia). clear AvC.
        unfold MallocRep.wz.

      pose proof EVg as (_ & _ & STg & MIg & _ & _ & _ & _ & FRg & FSZg & _). cbn [app locs] in FRg.
        pose proof (obj_arrA (q1, f + 32, 256) ((q2, f + 352, 64) :: LB) PL lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls OW mb _ _ _ _ _ _ ws EVg VB
                      ltac:(cbn [blk_size snd]; rewrite LEN; reflexivity) ltac:(cbn [blk_addr blk_size fst snd]; intros xq Hxq; apply NFVP; clear - Hxq; lia)) as VA.
        cbn [blk_addr fst snd] in VA.
        pose proof (obj_acc _ _ _ _ (q1, f + 32, 256) HEAPg ltac:(left; reflexivity)) as ACCV. cbn [blk_addr blk_size fst snd] in ACCV.
        assert (IDX : 0 <= Z.of_nat (length vals) < Z.of_nat (length ws)) by (rewrite LEN; clear - K32; lia).
        assert (XR : 0 <= f + 32 + 8 * (Z.of_nat (length vals) - 1) /\ f + 32 + 8 * Z.of_nat (length vals) + 8 <= f + 32 + 256 /\ f + 288 < 2 ^ 64) by (clear - K1 K32 G1 G3 C1 C2 C3; lia).
        pose proof (munch_refl [(f + 32, f + 288)]%Z mg) as MU. pose proof (wmono_refl bgbsegs mg) as WM.
        apply implA_from_evt.
        rewrite ?(unsigned_lit (32 - Z.of_nat (length vals))) by (clear - K32; lia).
        ub1 ub_kind.
        step. rewrite ?(unsigned_lit (f + 32 + 8 * Z.of_nat (length vals))) by (clear - XR; lia).
        step. shl_with ACCV ALV.
        step. chk0.
        pose proof (u64arr_store_ok bgbsegs mg (f + 32) ws (Z.of_nat (length vals)) (wa (f + 32 + 8 * Z.of_nat (length vals))) VA IDX eq_refl) as SOKW.
        pose proof (u64arr_write bgbsegs mg (f + 32) ws (Z.of_nat (length vals)) (Z_to_bv 64 av) VA IDX) as U2.
        clear ACCV.
        step. store_done.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mV end.
        rewrite Nat2Z.id in U2.
        destruct (cenv_objA (q1, f + 32, 256) ((q2, f + 352, 64) :: LB) PL EA lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls OW mb _ _ _ _ _ _ _ _ EVg LSg MU WM
                    ltac:(constructor; [cbn [blk_addr blk_size fst snd]; clear; lia | constructor])
                    ltac:(cbn [blk_addr blk_size fst snd]; intros xq Hxq; apply NFVP; clear - Hxq; lia) STg MIg) as (EVV & LSV & AXO).
        pose proof (ax_pres_trans _ _ _ _ _ _ AXB (ax_unplace _ _ _ _ _ _ _ _ _ EVV AXO)) as AXB2.
        pose proof U2 as VB2. apply hide_intro in VB2.
        clear MU WM STg MIg FRg FSZg EVg LSg HEAPg PARTSg.

        step. if_cases KZ; rewrite ?unsigned_lit in KZ by (clear - AvR; lia); zify_cond KZ; [exfalso; clear - KZ AvR; lia| clear KZ].

        pose proof U2 as VAL.
        pose proof VT as [VL VT']. pose proof (VT' (length vals - 1)%nat ltac:(clear - K1; lia)) as (Wp & HAprev & (jp & Eprev) & AprevR). clear VT'.
        assert (Wp' : nth_error (Arr.upd ws (length vals) (Z_to_bv 64 av)) (Z.to_nat (Z.of_nat (length vals) - 1)) = Some (Z_to_bv 64 (nth (length vals - 1) addrs 0))).
        { rewrite nth_error_upd_other by (clear - K1; lia). replace (Z.to_nat (Z.of_nat (length vals) - 1)) with (length vals - 1)%nat by (clear; lia). exact Wp. }
        let a := cur_mem_addr in pose proof (u64arr_read bgbsegs mV (f + 32) _ (Z.of_nat (length vals) - 1) _ a VAL Wp' ltac:(clear - K1; lia) ltac:(addr_tac)) as RD.
        step. clear RD VAL Wp'.
      pose proof EVV as (_ & _ & STV & MIV & _ & _ & _ & _ & FRV & FSZV & _). cbn [app locs] in FRV.
        step. step. step.
    apply evt_done.
        apply implA_tbind_assoc. eapply implA_bind.
        { rewrite last_nth. eapply (BN_mod_mul_reciprocal_walkA) with (lo := lo) (OW := OWg) (LB := ((q1, f + 32, 256) :: (q2, f + 352, 64) :: LB)) (PL := PL) (EA := EA);
            [| | | | reflexivity | exact HAv | exact (ref_at_stable _ _ _ _ PL _ _ RSg HAprev) | exact (ref_at_stable _ _ _ _ PL _ _ RSg HAd) | rewrite Ev; apply hpl_pool | rewrite Eprev; unfold RPool, ROne, NFIX; clear; lia | exact NROd | rewrite Eprev; apply nbuf_pool | rewrite Ed; apply nbuf_pool | exact HRC | exact INQ2 | exact AL8 | exact HPCP | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity].
          - eapply cenv_preA; [exact EVV | exact LSV | clear - LOK; lia | clear - KCOST CMM0; lia].
          - eapply cenv_roomA; [exact EVV | exact ROOM | clear; lia].
          - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EVV).
          - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_BN_mod_exp_recp_2ba488 CTX).
        }
        cbv beta. intros [um lsm] Σm msm PO.
        apply (bn_postA_cpost ((q1, f + 32, 256) :: (q2, f + 352, 64) :: LB) PL EA lo (bv_unsigned sp) spa TOTAL Σ1 ls OW) in PO; [| exact OK | exact (proj1 (proj2 EVV))].
        cbn [fst snd] in *.
        destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & Fm & fcm & mm & OWm & PLm & -> & CPm & (EPLm & ->)).
        subst PLm. specialize (CPm eq_refl).
        destruct (cenv_postA ((q1, f + 32, 256) :: (q2, f + 352, 64) :: LB) PL EA lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls OW mV _ _ _ _ _ _ _ _ _ _ _ EVV CPm) as (EVm & LSm).
        pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CPm) as RSm. clear CPm.
        rewrite (ret_pc_even 2860656) by (clear; lia).
        pose proof (refs_stable_trans _ _ _ _ _ _ RSg RSm) as RSgm.
      pose proof EVm as (_ & _ & STm & MIm & _ & _ & _ & _ & FRm & FSZm & _). cbn [app locs] in FRm.
        unfold MallocRep.wz. apply implA_from_evt. step. step. if_false.
        apply evt_done.
        eapply (CONT2 ug av mV _ _ _ _ (Arr.upd ws (length vals) (Z_to_bv 64 av)));
          [ replace (used + MC + CMM) with (used + MC + CMM) by reflexivity; exact EVm | exact LSm | exact AXB2 | apply hide_elim in VB2; exact VB2 | etransitivity; [apply Arr.upd_length| exact LEN] |
          | exact (ref_at_stable _ _ _ _ PL _ _ RSgm HAd) | exact RSgm].
        apply (vtab_stable lsg OWg); [|exact RSm]. eapply vtab_snoc; [eapply vtab_stable; [exact VT| exact RSg]| rewrite LEN; exact K32| exact HAv| exact Ev| exact AvR].
      Qed.

      Lemma table_loopA : forall c vals addrs mb used ΣK lsK mK OWK ws (bits window : Z) (d : bnref) (ad : Z) (di : nat)
          (w0 w3 w8 w9 : word) (x1 t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
        CENV mb (locs w0 (Z_to_bv 64 window) (Z_to_bv 64 (window - 1)) w3 (Z_to_bv 64 bits) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 ad) (Z_to_bv 64 AN) w8 w9 ++ [CB g junk]) used ΣK lsK mK OWK ->
        lib_state lsK mK OWK PL EA -> ax_pres LB (bv_unsigned sp) (XW PL0) m1 mb ->
        u64arr bgbsegs mb (f + 32) ws -> length ws = 32%nat ->
        vtab lsK OWK ws vals addrs -> (1 <= length vals)%nat -> Z.of_nat (length vals) + Z.of_nat (S c) = 2 ^ (window - 1) -> 1 < window <= 6 -> 0 < bits <= 32768 ->
        ref_at lsK OWK PL d ad -> d = RPool di ->
        used + Z.of_nat (S c) * (MC + CMM) + MC + 2 * bits * CMM <= TOTAL ->
        implA (tbind (exp_table_loop (tree_ops bptr) MUL (S c) vals d lsK) (fun p => tbind (restm bits window (fst p) (snd p)) ENDK)) ΣK Q
          (MS (mkR x1 (Z_to_bv 64 spa) gp (Z_to_bv 64 TP_A) t0 t1 t2 sp (Z_to_bv 64 spa) a0 (Z_to_bv 64 (Z.of_nat (length vals) + 1)) a2 a3 a4 a5 a6 a7
                         (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) (Z_to_bv 64 ac) (Z_to_bv 64 arr) (Z_to_bv 64 arp) (Z_to_bv 64 f) (Z_to_bv 64 (f + 32 + 8 * Z.of_nat (length vals))) (Z_to_bv 64 (f + 32 + 8 * Z.of_nat (length vals))) (Z_to_bv 64 SHB) (Z_to_bv 64 (32 - Z.of_nat (length vals))) t3 t4 t5 t6)
                    F (Z_to_bv 64 2860596) fc None mK (seg_rom bgbsegs)).
      Proof.
        induction c as [|c IH]; intros until fc; intros EVK LSK AXB VB LEN VT K1 KC WB BITS HAd Ed KCOST.
        -
          rewrite exp_table_loop_S. apply implA_tbind_assoc.
          assert (TS : 2 ^ (window - 1) <= 32) by (replace 32 with (2 ^ 5) by reflexivity; apply Z.pow_le_mono_r; lia).
          eapply (table_bodyA vals addrs mb used ΣK lsK mK OWK ws bits window d ad di
                    (fun v ls' => exp_table_loop (tree_ops bptr) MUL 0 (vals ++ [v]) d ls') (fun p => tbind (restm bits window (fst p) (snd p)) ENDK));
            [exact EVK| exact LSK| exact AXB| exact VB| exact LEN| exact VT| exact K1| clear - KC TS; lia| exact WB| exact HAd| exact Ed
            | pose proof MC0 as MCP; clear - KCOST MCP CMM0 BITS; nia|].
          intros v av mb2 Σ2 ls2 m2 OW2 ws2 x1' t0' t1' t2' a0' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' EV2 LS2 AXB2 VB2 LEN2 VT2 HAd2 RS2.
          cbv beta. rewrite exp_table_loop_O. cbn [tbind fst snd].
          kit EV2.
          assert (TS1 : 1 <= 2 ^ (window - 1)) by (clear - WB; assert (0 < 2 ^ (window - 1)) by (apply Z.pow_pos_nonneg; lia); lia).
      pose proof EV2 as (_ & _ & STx & MIx & _ & _ & _ & _ & FRx & FSZx & _). cbn [app locs] in FRx.
          apply implA_from_evt.
          step.
          step. rewrite !unsigned_lit by (clear - KC TS WB; lia). rewrite (bv_wrap_small 32) by (unfold bv_modulus; clear - KC TS; lia).
          rewrite (Z.mod_small (window - 1) 32) by (clear - WB; lia). rewrite Z.shiftr_div_pow2 by (clear - WB; lia).
          replace ((Z.of_nat (length vals) + 1) / 2 ^ (window - 1)) with 1 by (symmetry; replace (Z.of_nat (length vals) + 1) with (2 ^ (window - 1)) by (clear - KC; lia); apply Z.div_same; clear - TS1; lia).
          rewrite (bn_swrap32_small 1) by (clear; lia).
          step. step. step. step.
          step. if_false.
          step. step.
          apply evt_done.
          eapply (L_restA mb2 _ _ _ _ _ ws2 (vals ++ [v]) (addrs ++ [av]) bits window);
            [exact EV2| exact LS2| exact AXB2| exact VB2| exact LEN2| exact VT2
            | rewrite length_app; cbn [length]; replace (1 <? window) with true by (symmetry; apply Z.ltb_lt; clear - WB; lia); clear - KC; lia
            | clear - WB; lia| exact BITS| pose proof MC0 as MCP'; clear - KCOST MCP' CMM0; nia].
        -
          rewrite exp_table_loop_S. apply implA_tbind_assoc.
          assert (TS : 2 ^ (window - 1) <= 32) by (replace 32 with (2 ^ 5) by reflexivity; apply Z.pow_le_mono_r; lia).
          assert (BC : 0 <= bits * CMM) by (apply Z.mul_nonneg_nonneg; [clear - BITS; lia | exact CMM0]).
          assert (CC : 0 <= Z.of_nat (S c) * (MC + CMM)) by (apply Z.mul_nonneg_nonneg; [clear; lia | pose proof MC0; clear - H CMM0; lia]).
          eapply (table_bodyA vals addrs mb used ΣK lsK mK OWK ws bits window d ad di
                    (fun v ls' => exp_table_loop (tree_ops bptr) MUL (S c) (vals ++ [v]) d ls') (fun p => tbind (restm bits window (fst p) (snd p)) ENDK));
            [exact EVK| exact LSK| exact AXB| exact VB| exact LEN| exact VT| exact K1| clear - KC TS; lia| exact WB| exact HAd| exact Ed
            | pose proof MC0 as MCP; replace (Z.of_nat (S (S c))) with (Z.of_nat (S c) + 1) in KCOST by (clear; lia); clear - KCOST MCP CMM0 BC CC; lia|].
          intros v av mb2 Σ2 ls2 m2 OW2 ws2 x1' t0' t1' t2' a0' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' EV2 LS2 AXB2 VB2 LEN2 VT2 HAd2 RS2.
          cbv beta.
          kit EV2.
      pose proof EV2 as (_ & _ & STx & MIx & _ & _ & _ & _ & FRx & FSZx & _). cbn [app locs] in FRx.
          apply implA_from_evt.
          step.
          step. rewrite !unsigned_lit by (clear - KC TS WB; lia). rewrite (bv_wrap_small 32) by (unfold bv_modulus; clear - KC TS; lia).
          rewrite (Z.mod_small (window - 1) 32) by (clear - WB; lia). rewrite Z.shiftr_div_pow2 by (clear - WB; lia).
          rewrite (Z.div_small (Z.of_nat (length vals) + 1) (2 ^ (window - 1))) by (clear - KC; lia).
          rewrite (bn_swrap32_small 0) by (clear; lia).
          step. step. step. step.
          step. if_true.
          rewrite ?(unsigned_lit (32 - Z.of_nat (length vals))) by (clear - KC TS; lia).
          replace (Z.of_nat (length vals) + 2) with (Z.of_nat (length (vals ++ [v])) + 1) by (rewrite length_app; cbn [length]; clear; lia).
          replace (f + 32 + 8 * Z.of_nat (length vals) + 8) with (f + 32 + 8 * Z.of_nat (length (vals ++ [v]))) by (rewrite length_app; cbn [length]; clear; lia).
          replace (32 - Z.of_nat (length vals) + -1) with (32 - Z.of_nat (length (vals ++ [v]))) by (rewrite length_app; cbn [length]; clear; lia).
          apply evt_done.
          eapply (IH (vals ++ [v]) (addrs ++ [av]) mb2 _ _ _ _ _ ws2 bits window d ad di);
            [exact EV2| exact LS2| exact AXB2| exact VB2| exact LEN2| exact VT2| rewrite length_app; cbn [length]; clear; lia
            | rewrite length_app; cbn [length]; clear - KC; lia| exact WB| exact BITS| exact HAd2| exact Ed
            | replace (Z.of_nat (S (S c))) with (Z.of_nat (S c) + 1) in KCOST by (clear; lia); clear - KCOST; lia].
      Qed.

      Lemma vtab_one : forall lsK OWK ws v0 av0 vi, nth_error ws 0 = Some (Z_to_bv 64 av0) -> ref_at lsK OWK PL v0 av0 -> v0 = RPool vi -> 0 < av0 < 2 ^ 64 ->
        vtab lsK OWK ws [v0] [av0].
      Proof.
        intros lsK OWK ws v0 av0 vi W0 HAv Ev AvR. split; [reflexivity|]. intros i Hi. cbn [length] in Hi. assert (Ei : i = 0%nat) by (clear - Hi; lia). subst i. cbn [nth].
        split; [exact W0|]. split; [exact HAv|]. split; [exists vi; exact Ev| exact AvR].
      Qed.

      Lemma L_nonzeroA : forall mb used ΣK lsK mK OWK ws (bits : Z) (d v0 : bnref) (ad av0 : Z) (di vi : nat)
          (w0 w1 w2 w3 w8 w9 : word) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x24 x25 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
        CENV mb (locs w0 w1 w2 w3 (Z_to_bv 64 bits) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 ad) (Z_to_bv 64 AN) w8 w9 ++ [CB g junk]) used ΣK lsK mK OWK ->
        lib_state lsK mK OWK PL EA -> ax_pres LB (bv_unsigned sp) (XW PL0) m1 mb ->
        u64arr bgbsegs mb (f + 32) ws -> length ws = 32%nat -> nth_error ws 0 = Some (Z_to_bv 64 av0) ->
        ref_at lsK OWK PL d ad -> d = RPool di -> ref_at lsK OWK PL v0 av0 -> v0 = RPool vi -> 0 < av0 < 2 ^ 64 -> 0 < bits <= 32768 ->
        used + CMM + 31 * (MC + CMM) + MC + 2 * bits * CMM <= TOTAL ->
        implA (tbind (tbind (exp_table (tree_ops bptr) MUL (window_bits bits) v0 d lsK) (fun p => restm bits (window_bits bits) (fst p) (snd p))) ENDK) ΣK Q
          (bst x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x24 x25 (Z_to_bv 64 (f + 32)) t3 t4 t5 t6 F 2860464 fc mK).
      Proof.
        intros until fc; intros EVK LSK AXB VB LEN W0 HAd Ed HAv Ev AvR BITS KCOST. kitg EVK. unfold bst, MallocRep.wz in *.
        assert (NROd : d <> ROne) by (rewrite Ed; unfold RPool, ROne, NFIX; clear; lia).
        assert (NROv : v0 <> ROne) by (rewrite Ev; unfold RPool, ROne, NFIX; clear; lia).
        assert (BC : 0 <= bits * CMM) by (apply Z.mul_nonneg_nonneg; [clear - BITS; lia | exact CMM0]).
        assert (XR : 0 <= f + 32 /\ f + 288 < 2 ^ 64) by (clear - G1 G3 C1 C2 C3; lia).
        apply implA_tbind_assoc.
        remember (window_bits bits) as window eqn:EW.
        assert (TBL : forall (x1' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32), 1 < window <= 6 ->
                  implA (tbind (exp_table (tree_ops bptr) MUL window v0 d lsK) (fun p => tbind (restm bits window (fst p) (snd p)) ENDK)) ΣK Q
                    (MS (mkR x1' (Z_to_bv 64 spa) gp (Z_to_bv 64 TP_A) t0' t1' t2' sp (Z_to_bv 64 spa) (Z_to_bv 64 ad) a1' a2' a3' a4' a5' a6' a7'
                         (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) (Z_to_bv 64 ac) (Z_to_bv 64 arr) (Z_to_bv 64 arp) (Z_to_bv 64 f) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 window) (Z_to_bv 64 SHB) (Z_to_bv 64 AN) t3' t4' t5' t6')
                    F' (Z_to_bv 64 2860544) fc' None mK (seg_rom bgbsegs))).
        { intros until fc'. intros WB.
          assert (P2 : 2 <= 2 ^ (window - 1) <= 32).
          { split; [change 2 with (2 ^ 1) at 1| change 32 with (2 ^ 5)]; apply Z.pow_le_mono_r; clear - WB; lia. }
          unfold exp_table. replace (1 <? window) with true by (symmetry; apply Z.ltb_lt; clear - WB; lia).
          unfold bbind. cbn [bind tree_ops].
          replace (Z.to_nat (2 ^ (window - 1)) - 1)%nat with (S (Z.to_nat (2 ^ (window - 1)) - 2)) by (clear - P2; lia).
      pose proof EVK as (_ & _ & STK & MIK & _ & _ & _ & _ & FRK & FSZK & _). cbn [app locs] in FRK.

          pose proof (obj_arrA (q1, f + 32, 256) ((q2, f + 352, 64) :: LB) PL lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls OW mb _ _ _ _ _ _ ws EVK VB
                        ltac:(cbn [blk_size snd]; rewrite LEN; reflexivity) ltac:(cbn [blk_addr blk_size fst snd]; intros xq Hxq; apply NFVP; clear - Hxq; lia)) as VA.
          cbn [blk_addr fst snd] in VA.
          assert (W0' : nth_error ws (Z.to_nat 0) = Some (Z_to_bv 64 av0)) by exact W0.
          apply implA_from_evt.
          let a := cur_mem_addr in pose proof (u64arr_read bgbsegs mK (f + 32) _ 0 _ a VA W0' ltac:(clear; lia) ltac:(addr_tac)) as RD.
          step. clear RD VA W0'.
          step. step. step. step.
    apply evt_done.
          apply implA_tbind_assoc. eapply implA_bind.
          { eapply (BN_mod_mul_reciprocal_walkA) with (lo := lo) (OW := OWK) (LB := ((q1, f + 32, 256) :: (q2, f + 352, 64) :: LB)) (PL := PL) (EA := EA);
              [| | | | reflexivity | exact HAd | exact HAv | exact HAv | rewrite Ed; apply hpl_pool | exact NROv | exact NROv | rewrite Ev; apply nbuf_pool | rewrite Ev; apply nbuf_pool | exact HRC | exact INQ2 | exact AL8 | exact HPCP | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity].
            - eapply cenv_preA; [exact EVK | exact LSK | clear - LOK; lia | clear - KCOST MCP CMM0 BC; lia].
            - eapply cenv_roomA; [exact EVK | exact ROOM | clear; lia].
            - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EVK).
            - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_BN_mod_exp_recp_2ba42c CTX).
          }
          cbv beta. intros [ud lsd] Σd msd PO.
          apply (bn_postA_cpost ((q1, f + 32, 256) :: (q2, f + 352, 64) :: LB) PL EA lo (bv_unsigned sp) spa TOTAL Σ1 ls OW) in PO; [| exact OK | exact (proj1 (proj2 EVK))].
          cbn [fst snd] in *.
          destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & Fd & fcd & md & OWd & PLd & -> & CPd & (EPLd & ->)).
          subst PLd. specialize (CPd eq_refl).
          destruct (cenv_postA ((q1, f + 32, 256) :: (q2, f + 352, 64) :: LB) PL EA lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls OW mb _ _ _ _ _ _ _ _ _ _ _ EVK CPd) as (EVd & LSd).
          pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CPd) as RSd. clear CPd.
          rewrite (ret_pc_even 2860564) by (clear; lia).
          unfold MallocRep.wz. apply implA_from_evt. step. if_false.
      pose proof EVd as (_ & _ & STd & MId & _ & _ & _ & _ & FRd & FSZd & _). cbn [app locs] in FRd.
          pose proof (munch_refl [(spa, spa + 88)]%Z md) as MU. pose proof (wmono_refl bgbsegs md) as WM.
          step. step. rewrite ?(unsigned_lit window) by (clear - WB; lia). step.
          step. rewrite ?(unsigned_lit (f + 32)) by (clear - XR; lia).
          step. step. step.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mT end.
          relocal EVd LSd MU WM STd MId FRd FSZd EVt LSt. clear MU WM STd MId FSZd.
          replace (window + -1) with (window - 1) in * by (clear; lia).
          replace (f + 40) with (f + 32 + 8 * Z.of_nat (length [v0])) by (cbn [length]; clear; lia).
          replace (Z_to_bv 64 2) with (Z_to_bv 64 (Z.of_nat (length [v0]) + 1)) by reflexivity.
          replace (Z_to_bv 64 31) with (Z_to_bv 64 (32 - Z.of_nat (length [v0]))) by reflexivity.
          apply evt_done.
          assert (TC : 0 <= (32 - 2 ^ (window - 1)) * (MC + CMM)) by (apply Z.mul_nonneg_nonneg; [clear - P2; lia | clear - MCP CMM0; lia]).
          eapply (table_loopA (Z.to_nat (2 ^ (window - 1)) - 2) [v0] [av0] mb _ _ _ mT _ ws bits window d ad di);
            [exact EVt| exact LSt| exact AXB| exact VB| exact LEN
            | exact (vtab_one _ _ ws v0 av0 vi W0 (ref_at_stable _ _ _ _ PL _ _ RSd HAv) Ev AvR)
            | cbn [length]; clear; lia| cbn [length]; clear - P2; lia| exact WB| exact BITS| exact (ref_at_stable _ _ _ _ PL _ _ RSd HAd)| exact Ed
            | replace (Z.of_nat (S (Z.to_nat (2 ^ (window - 1)) - 2))) with (2 ^ (window - 1) - 1) by (clear - P2; lia); clear - KCOST TC MCP CMM0; lia]. }
        unfold window_bits in EW.
      pose proof EVK as (_ & _ & STK & MIK & _ & _ & _ & _ & FRK & FSZK & _). cbn [app locs] in FRK.
        pose proof (munch_refl [(spa, spa + 88)]%Z mK) as MU. pose proof (wmono_refl bgbsegs mK) as WM.
        apply implA_from_evt.
        step. step. step. step.
        step. rewrite lts_signed by (clear - BITS; lia).
        destruct (Z.ltb_spec 671 bits) as [B1|B1]; cbn [negb].
        { assert (WV : window = 6) by (rewrite EW; repeat match goal with |- context [?a <? bits] => destruct (Z.ltb_spec a bits); [try (exfalso; lia)| try (exfalso; lia)] end; reflexivity).
          rewrite WV in TBL |- *. step. step. step. apply evt_done. eapply TBL. clear; lia. }
        step. step.
        step. rewrite lts_signed by (clear - BITS; lia).
        destruct (Z.ltb_spec 239 bits) as [B2|B2]; cbn [negb].
        { assert (WV : window = 5) by (rewrite EW; repeat match goal with |- context [?a <? bits] => destruct (Z.ltb_spec a bits); [try (exfalso; lia)| try (exfalso; lia)] end; reflexivity).
          rewrite WV in TBL |- *. step. step. apply evt_done. eapply TBL. clear; lia. }
        step.
        step. rewrite lts_signed by (clear - BITS; lia).
        destruct (Z.ltb_spec 79 bits) as [B3|B3]; cbn [negb].
        { assert (WV : window = 4) by (rewrite EW; repeat match goal with |- context [?a <? bits] => destruct (Z.ltb_spec a bits); [try (exfalso; lia)| try (exfalso; lia)] end; reflexivity).
          rewrite WV in TBL |- *. step. step. apply evt_done. eapply TBL. clear; lia. }
        step.
        step. rewrite lts_signed by (clear - BITS; lia).
        destruct (Z.ltb_spec bits 24) as [B4|B4].
        2:{ assert (WV : window = 3) by (rewrite EW; repeat match goal with |- context [?a <? bits] => destruct (Z.ltb_spec a bits); [try (exfalso; lia)| try (exfalso; lia)] end; reflexivity).
            rewrite WV in TBL |- *. step. apply evt_done. eapply TBL. clear; lia. }

        assert (WV : window = 1) by (rewrite EW; repeat match goal with |- context [?a <? bits] => destruct (Z.ltb_spec a bits); [try (exfalso; lia)| try (exfalso; lia)] end; reflexivity).
        step. lstep 1.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mW end.
        relocal EVK LSK MU WM STK MIK FRK FSZK EVW LSW. clear MU WM STK MIK FSZK.
        subst window. rewrite WV.
        replace (exp_table (tree_ops bptr) MUL 1 v0 d lsK) with (bret (tree_ops bptr) [v0] lsK) by reflexivity.
        rewrite tbind_bret. cbv beta. cbn [fst snd].
        apply evt_done.
        eapply (L_restA mb used _ _ _ _ ws [v0] [av0] bits 1);
          [exact EVW| exact LSW| exact AXB| exact VB| exact LEN| exact (vtab_one _ _ ws v0 av0 vi W0 HAv Ev AvR)| reflexivity| clear; lia| exact BITS
          | clear - KCOST MCP CMM0 BC; lia].
      Qed.

      Lemma body_main : forall (ra' u0 u1 u2 x10 x11 x12 x13 b4 b5 b6 b7 u3 u4 u5 u6 s11 : word) (F' : bvmap 5 word) (fc' : bv 32)
          (j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 : list byte),
        CENV0 m1 ([CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3; CB 8 j4; CB 8 j5; CB 8 j6; CB 8 j7; CB 8 j8; CB 8 j9; C8 (Z_to_bv 64 f)] ++ [CB g junk]) 0 Σ1 ls m1 OW ->
        lib_state ls m1 OW PL0 EA ->
        implA (BN_mod_exp_recp (tree_ops bptr) rr ra_ rp rm ls) Σ1 Q
          (MS (mkR ra' (Z_to_bv 64 spa) gp (wz TP_A) u0 u1 u2 sp (Z_to_bv 64 spa) x10 x11 x12 x13 b4 b5 b6 b7
                   (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) (wz ac) (wz arr) (wz arp) (Z_to_bv 64 f) (wz ara) (wz arm) (Z_to_bv 64 SHB) s11 u3 u4 u5 u6)
              F' (wz EXP_RECP_BODY) fc' None m1 (seg_rom bgbsegs)).
      Proof.
        intros until j9. intros EV0 LS0. kit EV0. unfold MallocRep.wz, EXP_RECP_BODY in *.
        pose proof (proj1 (proj2 EV0)) as HEAP0.
        pose proof (AH_nodup_l _ _ _ _ HEAP0) as ND.
        pose proof (lib_state_h_parts _ _ _ _ _ _ LS0) as PARTS.
        assert (ArR : 0 < arr < 2^64) by (pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP0 PARTS FROKK HAr (proj1 (hpl_wref _ _ WRr))) as (X & Y & _); unfold BnHeapA.ACEIL in *; clear - X Y C1 C2 C3; lia).
        assert (AmR : 0 < arm < 2^64) by (pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP0 PARTS FROKK HAm NROm) as (X & Y & _); unfold BnHeapA.ACEIL in *; clear - X Y C1 C2 C3; lia).
        assert (ApR : 0 < arp < 2^64) by (pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP0 PARTS FROKK HAp NROp) as (X & Y & _); unfold BnHeapA.ACEIL in *; clear - X Y C1 C2 C3; lia).

        set (ba := getbn ra_ ls). set (bp := getbn rp ls). set (bm := getbn rm ls).
        pose proof (st_wf_ok _ _ (proj1 PARTS) (ref_at_valid _ _ _ _ _ _ _ _ LS0 HAa) NROa) as (_ & _ & _ & OKa4). fold ba in OKa4.
        pose proof (st_wf_ok _ _ (proj1 PARTS) (ref_at_valid _ _ _ _ _ _ _ _ LS0 HAp) NROp) as (OKp1 & OKp2 & OKp3 & OKp4). fold bp in OKp1, OKp2, OKp3, OKp4.
        pose proof (st_wf_ok _ _ (proj1 PARTS) (ref_at_valid _ _ _ _ _ _ _ _ LS0 HAm) NROm) as (_ & _ & _ & OKm4). fold bm in OKm4.
        unfold BG_DMAX in OKp3.
        assert (CTa : Z.land (bn_flags ba) 4 = 0) by (destruct OKa4 as [E|E]; rewrite E; reflexivity).
        assert (CTp : Z.land (bn_flags bp) 4 = 0) by (destruct OKp4 as [E|E]; rewrite E; reflexivity).
        assert (CTm : Z.land (bn_flags bm) 4 = 0) by (destruct OKm4 as [E|E]; rewrite E; reflexivity).
        clear OKa4 OKp4 OKm4.

        unfold BN_mod_exp_recp, any_consttime, BN_num_bits, bbind, bget, bret, bunr. cbn [bind ret unreachable tree_ops tbind fst snd fold_right]. cbv beta.
        fold ba bp bm.
        apply implA_from_evt.

        step. step. step.
    eapply (get_flags_callA ((q1, f + 32, 256) :: (q2, f + 352, 64) :: LB) PL0 EA lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls OW m1 LOFB16); [exact EV0 | exact LS0 | exact HAp | exact NROp |].
      intros mA y0A y1A y2A y4A y5A y6A y7A y8A y9A y10A y11A y12A y13A y14A EVA LSA.
        rewrite (ret_pc_even 2859568) by (clear; lia).
        fold bp. rewrite (unsigned_lit 4) by (clear; lia). rewrite CTp.
        step. if_false.

        step. step. step.
    eapply (get_flags_callA ((q1, f + 32, 256) :: (q2, f + 352, 64) :: LB) PL0 EA lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls OW m1 LOFB16); [exact EVA | exact LSA | exact HAa | exact NROa |].
      intros mB y0B y1B y2B y4B y5B y6B y7B y8B y9B y10B y11B y12B y13B y14B EVB LSB.
        rewrite (ret_pc_even 2859584) by (clear; lia).
        fold ba. rewrite (unsigned_lit 4) by (clear; lia). rewrite CTa.
        step. if_false.

        step. step. step.
    eapply (get_flags_callA ((q1, f + 32, 256) :: (q2, f + 352, 64) :: LB) PL0 EA lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls OW m1 LOFB16); [exact EVB | exact LSB | exact HAm | exact NROm |].
      intros mC y0C y1C y2C y4C y5C y6C y7C y8C y9C y10C y11C y12C y13C y14C EVC LSC.
        rewrite (ret_pc_even 2859600) by (clear; lia).
        fold bm. rewrite (unsigned_lit 4) by (clear; lia). rewrite CTm.
        step. if_true.
        unfold has_flag, BN_FLG_CONSTTIME. rewrite CTa, CTp, CTm. cbn [Z.eqb negb orb andb].

        step. step.
    eapply (num_bits_callA ((q1, f + 32, 256) :: (q2, f + 352, 64) :: LB) PL0 EA lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls OW m1 ); [exact EVC | exact LSC | exact HAp | exact NROp | unfold BN_NUM_BITS_STACK in *; clear - LOK CSnb; lia |].
      intros mD y0D y1D y2D y4D y5D y6D y7D y8D y9D y10D y11D y12D y13D y14D EVD LSD.
        rewrite (ret_pc_even 2860160) by (clear; lia).
        pose proof (num_bits_pure_range bp OKp1) as BITS.
        fold bp. rewrite CTp. cbn [Z.eqb negb tbind]. cbv beta.
        set (bits := num_bits_pure bp) in *.
        step. if_cases KB; rewrite ?unsigned_lit in KB by (clear - BITS OKp2 OKp3; lia); zify_cond KB.
        {
          cbn [fst snd]. rewrite KB. cbn [Z.eqb]. unfold exp_bits0, bbind, bget. cbn [bind ret tree_ops tbind fst snd].
          fold bm.
          assert (T0 : 0 <= TOTAL) by (pose proof TOTAL_OK as H; unfold EXP_RECP_TOTAL, BN_NNMOD_COST, BN_DIV_FT_COST in H; clear - H MCP CMM0; lia).
          step. step. step. step.
    eapply (abs_is_word_callA ((q1, f + 32, 256) :: (q2, f + 352, 64) :: LB) PL0 EA lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls OW m1 LOFB16); [exact EVD | exact LSD | exact HAm | exact NROm |].
        intros mF y0F y1F y2F y4F y5F y6F y7F y8F y9F y10F y11F y12F y13F y14F EVF LSF.
          rewrite (ret_pc_even 2860352) by (clear; lia).
          fold bm. rewrite (unsigned_lit 1) by (clear; lia).
          destruct (abs_is_word_pure bm 1); cbn [Z.b2z].
          -
            step. if_false. step. step.
            eapply (ExpBodyKitF.zero_callA ((q1, f + 32, 256) :: (q2, f + 352, 64) :: LB) PL0 EA lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls OW m1 LOFB16); [exact EVF | exact LSF | exact HAr | exact (hpl_wref _ _ WRr) |].
            intros mG z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 lsG EVG LSG.
            rewrite (ret_pc_even 2860364) by (clear; lia).
            unfold BN_zero, bbind, bget, bset. cbn [bind ret tree_ops tbind fst snd].
            step.
            apply evt_done. eapply CONT; [exact EVG | exact LSG | exact T0 | apply ax_pres_refl | reflexivity].
          -
            step. if_true. step. step. step.
            unfold BN_one.
    apply evt_done.
            eapply implA_post.
            { eapply (BN_set_word_walkA) with (lo := lo) (OW := OW) (LB := ((q1, f + 32, 256) :: (q2, f + 352, 64) :: LB)) (PL := PL0) (EA := EA) (w := 1);
                [| | | reflexivity | exact HAr | exact (hpl_wref _ _ WRr) | reflexivity | reflexivity | clear; lia].
              - eapply cenv_preA; [exact EVF | exact LSF | clear - LOK CSsetw; lia | pose proof TOTAL_OK as H; unfold EXP_RECP_TOTAL, BN_NNMOD_COST, BN_DIV_FT_COST in H; clear - H MCP CMM0; lia].
              - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EVF).
              - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_BN_mod_exp_recp_2ba3c0 CTX).
            }
            cbv beta. intros [uH lsH] ΣH msH PO.
            apply (bn_postA_cpost ((q1, f + 32, 256) :: (q2, f + 352, 64) :: LB) PL0 EA lo (bv_unsigned sp) spa TOTAL Σ1 ls OW) in PO; [| exact OK | exact (proj1 (proj2 EVF))].
            cbn [fst snd] in *.
            destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & FH & fcH & mH & OWH & PLH & -> & CPH & (EPLH & -> & INCLH)).
            subst PLH. specialize (CPH eq_refl).
            destruct (cenv_postA ((q1, f + 32, 256) :: (q2, f + 352, 64) :: LB) PL0 EA lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls OW m1 _ _ _ _ _ _ _ _ _ _ _ EVF CPH) as (EVH & LSH).
            pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CPH) as RSH. clear CPH.
            rewrite (ret_pc_even 2860456) by (clear; lia).
            apply implA_from_evt. step. step.
            apply evt_done. destruct uH. eapply CONT; [exact EVH | exact LSH | pose proof TOTAL_OK as H; unfold EXP_RECP_TOTAL, BN_NNMOD_COST, BN_DIV_FT_COST in H; clear - H MCP CMM0; lia | apply ax_pres_refl | reflexivity]. }

        cbn [fst snd]. replace (bits =? 0) with false by (symmetry; apply Z.eqb_neq; exact KB).
        assert (BITSR : 0 < bits <= 32768) by (clear - KB BITS OKp2 OKp3; lia).
        fgeo HEAP0.
        assert (AL8 : (f + 352) mod 8 = 0) by (clear - G2; Z.div_mod_to_equations; lia).

        pose proof EVD as (_ & _ & STD & MID & _ & _ & _ & _ & FRD & FSZD & _). cbn [app] in FRD.
        pose proof (munch_refl [(spa, spa + 88)]%Z mD) as MU. pose proof (wmono_refl bgbsegs mD) as WM.
        step. step. step. step.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mL end.
        relocal EVD LSD MU WM STD MID FRD FSZD EVL LSL. clear MU WM STD MID FRD FSZD EVD LSD.

        unfold BN_RECP_CTX_init, bsetrecp, bset, bbind. cbn [bind ret tree_ops tbind fst snd].
        step.
        apply evt_done.
        eapply (recp_init_callA _ Q [(q1, f + 32, 256); (q2, f + 352, 64)] LB PL0 EA lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls OW m1 _ _ _ _ _ _ q2 (f + 352));
          [exact EVL | exact LSL | right; left; reflexivity | exact AL8 | intros xq Hxq; apply NFV; clear - Hxq; lia | exact HFN | exact HFNr | exact HFR
          | clear - LOK CSinit; lia | reflexivity |].
        intros mI y0I y1I y2I y3I y4I y5I y6I y7I y8I y9I y10I y11I y12I y13I y14I FI fcI EVI LSI AXI.
        unfold st_recp_init in EVI, LSI.
        set (lsI := setbn RRecpNr (bn_nil 0) (setbn RRecpN (bn_nil 0) (set_recp 0 0 ls))) in *.
        rewrite (ret_pc_even 2860184) by (clear; lia).
        clear EVL LSL OK FROKK. pose proof EVI as (OK & _). pose proof OK as (_ & _ & _ & _ & _ & _ & _ & _ & FROKK & _ & _).

        unfold MallocRep.wz. apply implA_from_evt. step. step.
    apply evt_done.
        eapply implA_bind.
        { eapply (BN_CTX_start_walkA) with (lo := lo) (OW := OW) (LB := ((q1, f + 32, 256) :: (q2, f + 352, 64) :: LB)) (PL := PL) (EA := EA);
            [| | | reflexivity | exact HPCP | reflexivity].
          - eapply cenv_preA; [exact EVI | exact LSI | clear - LOK CSstart; lia | pose proof TOTAL_OK as H; unfold EXP_RECP_TOTAL, BN_NNMOD_COST, BN_DIV_FT_COST in H |- *; clear - H MCP CMM0; lia].
          - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EVI).
          - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_BN_mod_exp_recp_2ba2b8 CTX).
        }
        cbv beta. intros [uc1 lsc1] Σc1 msc1 PO.
        apply (bn_postA_cpost ((q1, f + 32, 256) :: (q2, f + 352, 64) :: LB) PL EA lo (bv_unsigned sp) spa TOTAL Σ1 ls OW) in PO; [| exact OK | exact (proj1 (proj2 EVI))].
        cbn [fst snd] in *.
        destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & Fc1 & fcc1 & mc1 & OWc1 & PLc1 & -> & CPc1 & (EPLc1 & INCLc1)).
        subst PLc1. specialize (CPc1 eq_refl).
        destruct (cenv_postA ((q1, f + 32, 256) :: (q2, f + 352, 64) :: LB) PL EA lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls OW mI _ _ _ _ _ _ _ _ _ _ _ EVI CPc1) as (EVc1 & LSc1).
        pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CPc1) as RSc1. clear CPc1.
        rewrite (ret_pc_even 2860192) by (clear; lia).

        apply implA_from_evt. step. step.
    apply evt_done.
        eapply implA_bind.
        { eapply (BN_CTX_get_walkA) with (lo := lo) (OW := OWc1) (LB := ((q1, f + 32, 256) :: (q2, f + 352, 64) :: LB)) (PL := PL) (EA := EA);
            [| | | reflexivity | exact HPCP | reflexivity].
          - eapply cenv_preA; [exact EVc1 | exact LSc1 | clear - LOK CSget; lia | pose proof TOTAL_OK as H; unfold EXP_RECP_TOTAL, BN_NNMOD_COST, BN_DIV_FT_COST in H |- *; clear - H MCP CMM0; lia].
          - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EVc1).
          - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_BN_mod_exp_recp_2ba2c0 CTX).
        }
        cbv beta. intros [uc2 lsc2] Σc2 msc2 PO.
        apply (bn_postA_cpost ((q1, f + 32, 256) :: (q2, f + 352, 64) :: LB) PL EA lo (bv_unsigned sp) spa TOTAL Σ1 ls OW) in PO; [| exact OK | exact (proj1 (proj2 EVc1))].
        cbn [fst snd] in *.
        destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & Fc2 & fcc2 & mc2 & OWc2 & PLc2 & -> & CPc2 & (EPLc2 & (di & Ed) & (ad & HAd & ->) & INCLc2)).
        subst PLc2. specialize (CPc2 eq_refl).
        destruct (cenv_postA ((q1, f + 32, 256) :: (q2, f + 352, 64) :: LB) PL EA lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls OW mI _ _ _ _ _ _ _ _ _ _ _ EVc1 CPc2) as (EVc2 & LSc2).
        pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CPc2) as RSc2. clear CPc2.
        rewrite (ret_pc_even 2860200) by (clear; lia).

        pose proof EVc2 as (_ & _ & STc2 & MIc2 & _ & _ & _ & _ & FRc2 & FSZc2 & _). cbn [app] in FRc2.
        pose proof (munch_refl [(spa, spa + 88)]%Z mc2) as MU. pose proof (wmono_refl bgbsegs mc2) as WM.
        apply implA_from_evt. step.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mLc2 end.
        relocal EVc2 LSc2 MU WM STc2 MIc2 FRc2 FSZc2 EVLc2 LSLc2. clear MU WM STc2 MIc2 FRc2 FSZc2 EVc2 LSc2.

        step. step.
    apply evt_done.
        eapply implA_bind.
        { eapply (BN_CTX_get_walkA) with (lo := lo) (OW := OWc2) (LB := ((q1, f + 32, 256) :: (q2, f + 352, 64) :: LB)) (PL := PL) (EA := EA);
            [| | | reflexivity | exact HPCP | reflexivity].
          - eapply cenv_preA; [exact EVLc2 | exact LSLc2 | clear - LOK CSget; lia | pose proof TOTAL_OK as H; unfold EXP_RECP_TOTAL, BN_NNMOD_COST, BN_DIV_FT_COST in H |- *; clear - H MCP CMM0; lia].
          - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EVLc2).
          - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_BN_mod_exp_recp_2ba2cc CTX).
        }
        cbv beta. intros [uc3 lsc3] Σc3 msc3 PO.
        apply (bn_postA_cpost ((q1, f + 32, 256) :: (q2, f + 352, 64) :: LB) PL EA lo (bv_unsigned sp) spa TOTAL Σ1 ls OW) in PO; [| exact OK | exact (proj1 (proj2 EVLc2))].
        cbn [fst snd] in *.
        destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & Fc3 & fcc3 & mc3 & OWc3 & PLc3 & -> & CPc3 & (EPLc3 & (vi & Ev0) & (av0 & HAv0 & ->) & INCLc3)).
        subst PLc3. specialize (CPc3 eq_refl).
        destruct (cenv_postA ((q1, f + 32, 256) :: (q2, f + 352, 64) :: LB) PL EA lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls OW mI _ _ _ _ _ _ _ _ _ _ _ EVLc2 CPc3) as (EVc3 & LSc3).
        pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CPc3) as RSc3. clear CPc3.
        rewrite (ret_pc_even 2860212) by (clear; lia).

        pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 EVI)))))))) as RSI.
        pose proof (refs_stable_trans _ _ _ _ _ _ RSc1 (refs_stable_trans _ _ _ _ _ _ RSc2 RSc3)) as RSc03.
        pose proof (refs_stable_trans _ _ _ _ _ _ RSI RSc03) as RS03.
        pose proof (ref_at_stable _ _ _ _ PL _ _ RS03 HArP) as HArc3. pose proof (ref_at_stable _ _ _ _ PL _ _ RS03 HAaP) as HAac3.
        pose proof (ref_at_stable _ _ _ _ PL _ _ RS03 HApP) as HApc3. pose proof (ref_at_stable _ _ _ _ PL _ _ RS03 HAmP) as HAmc3.
        pose proof (ref_at_stable _ _ _ _ PL _ _ RSc3 HAd) as HAdc3.
        pose proof (proj1 (proj2 EVc3)) as HEAPc3. pose proof (lib_state_h_parts _ _ _ _ _ _ LSc3) as PARTSc3.
        assert (NROd : uc2 <> ROne) by (rewrite Ed; unfold RPool, ROne, NFIX; lia).
        assert (NROv0 : uc3 <> ROne) by (rewrite Ev0; unfold RPool, ROne, NFIX; lia).
        pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAPc3 PARTSc3 FROKK HAv0 NROv0) as (Av0 & AvC & _).
        assert (AvR : 0 < av0 < 2^64) by (unfold BnHeapA.ACEIL in *; clear - Av0 AvC C1 C2 C3; lia). clear AvC.
        pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAPc3 PARTSc3 FROKK HAdc3 NROd) as (Ad0 & AdC & _).
        assert (AdR : 0 < ad < 2^64) by (unfold BnHeapA.ACEIL in *; clear - Ad0 AdC C1 C2 C3; lia).

        pose proof EVc3 as (_ & _ & STc3 & MIc3 & _ & _ & _ & _ & FRc3 & FSZc3 & _). cbn [app] in FRc3.
        pose proof (munch_refl [(spa, spa + 88)]%Z mc3) as MU. pose proof (wmono_refl bgbsegs mc3) as WM.
        apply implA_from_evt. step.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mLc3 end.
        relocal EVc3 LSc3 MU WM STc3 MIc3 FRc3 FSZc3 EVLc3 LSLc3. clear MU WM STc3 MIc3 FRc3 FSZc3 EVc3 LSc3 HEAPc3 PARTSc3.

        destruct (AH_in_fr_pb _ _ _ _ f 3%nat (q1, f + 32, 256) (proj1 (proj2 EVLc3)) INF ltac:(apply in_or_app; right; left; reflexivity)
                    ltac:(split; cbn [blk_addr blk_size fst snd]; unfold fs_size; change (Z.shiftl 64 (Z.of_nat 3)) with 512; clear; lia)) as (_ & _ & WRV & _).
        cbn [blk_addr blk_size fst snd] in WRV.
        destruct (wr_at_rw_CB mLc3 (f + 32) 256 WRV ltac:(clear; lia)) as (jv & FRVc3). change (Z.to_nat 256) with 256%nat in FRVc3. clear WRV.
        pose proof EVLc3 as (_ & _ & STc3 & MIc3 & _).
        pose proof (munch_refl [(f + 32, f + 288)]%Z mLc3) as MU. pose proof (wmono_refl bgbsegs mLc3) as WM.
        step.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mV end.
        destruct (val_obj_init _ _ _ _ FRVc3) as (ws0 & LEN0 & WS0 & VB). clear FRVc3.
        destruct (cenv_objA (q1, f + 32, 256) ((q2, f + 352, 64) :: LB) PL EA lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls OW mI _ _ _ _ _ _ _ _ EVLc3 LSLc3 MU WM
                    ltac:(constructor; [cbn [blk_addr blk_size fst snd]; clear; lia | constructor])
                    ltac:(cbn [blk_addr blk_size fst snd]; intros xq Hxq; apply NFVP; clear - Hxq; lia) STc3 MIc3) as (EVV & LSV & AXO).
        pose proof (ax_pres_trans _ _ _ _ _ _ AXI (ax_unplace _ _ _ _ _ _ _ _ _ EVV AXO)) as AXB.
        clear MU WM STc3 MIc3 EVLc3 LSLc3 AXO AXI.
        apply hide_intro in VB.
        unfold MallocRep.wz.
        step. if_cases KZ; rewrite ?unsigned_lit in KZ by (clear - AvR; lia); zify_cond KZ; [exfalso; clear - KZ AvR; lia| clear KZ].

        pose proof EVV as EVW. pose proof LSV as LSW. clear EVV LSV.
        apply hide_elim in VB.

        pose proof (cenv_pre_wf _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ EVW) as WFI. cbn [cells_wf cell_wf app] in WFI.
        destruct WFI as (L0 & L1 & L2 & L3 & _ & _ & _ & _ & L8 & L9 & _ & LJ & _).
        destruct (cb8_word j0 L0) as (w0 & E0). destruct (cb8_word j1 L1) as (w1 & E1). destruct (cb8_word j2 L2) as (w2 & E2). destruct (cb8_word j3 L3) as (w3 & E3).
        destruct (cb8_word j8 L8) as (w8 & E8). destruct (cb8_word j9 L9) as (w9 & E9).
        lazymatch type of EVW with cenvA _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?u ?S ?l ?mm ?o =>
          assert (EVR : CENV mV (locs w0 w1 w2 w3 (Z_to_bv 64 bits) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 ad) (Z_to_bv 64 AN) w8 w9 ++ [CB g junk]) u S l mm o)
        end.
        { eapply cenv_recastA; [exact EVW | | |].
          - unfold locs. cbn [cells_wf cell_wf app]. repeat split; exact LJ.
          - unfold locs. cbn [cells_bytes cbytes app]. rewrite E0, E1, E2, E3, E8, E9. reflexivity.
          - reflexivity. }
        clear EVW.

        destruct (open_for_call ((q1, f + 32, 256) :: (q2, f + 352, 64) :: LB) PL EA lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls OW mV LOFB16 _ _ _ _ _ _ rm arm EVR LSW HAmc3 NROm)
          as (Dm & BNm & _ & _ & _ & _ & SEPm & _ & ACCm & ALm & _ & OFSm & Am0).
        unfold BnRepDefs.bn_cells, MallocRep.wz in BNm. unfold SHLO, SHHI in OFSm.
        pose proof SPT as SPT'. unfold USTACK_TOP in SPT'.
        assert (AmT : 0 <= arm /\ arm + 24 <= 140737488355328) by (clear - SEPm FBSP SPT' Am0; lia).
      pose proof EVR as (_ & _ & STR & MIR & _ & _ & _ & _ & FRR & FSZR & _). cbn [app locs] in FRR.
        pose proof (munch_refl (@nil (Z * Z)) mV) as MU0.
        step. step.
        hide_ors. ub. unhide.
        step. step. step.
        shl_with ACCm ALm. chk0.
        step. rewrite (sx32_int (Z.b2z (bn_neg (getbn rm lsc3)))) by (destruct (bn_neg (getbn rm lsc3)); cbn [Z.b2z]; clear; lia).
        clear BNm ACCm MU0.

        lazymatch goal with |- evt _ (fun ms' => implA (tbind _ ?rest) _ _ _) _ => set (REST := rest) end.
        assert (SETK : forall (rd : bnref) (adx used5 : Z) (Σ5 : rts RT) (ls5 : bstate bptr) (m5 : mem) (OW5 : list block)
                         (k1 k5 k6 k7 k12 k13 k14 k15 k16 k17 k28 k29 k30 k31 : word) (F5 : bvmap 5 word) (fc5 : bv 32),
                  CENV mV (locs w0 w1 w2 w3 (Z_to_bv 64 bits) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 ad) (Z_to_bv 64 AN) w8 w9 ++ [CB g junk]) used5 Σ5 ls5 m5 OW5 ->
                  lib_state ls5 m5 OW5 PL EA -> refs_stable lsc3 OWc3 ls5 OW5 ->
                  ref_at ls5 OW5 PL rd adx -> rd <> ROne -> used5 <= 0 + MC + MC + MC + MC ->
                  implA (tbind (BN_RECP_CTX_set (tree_ops bptr) rd ls5) REST) Σ5 Q
                    (MS (mkR k1 (Z_to_bv 64 spa) gp (Z_to_bv 64 TP_A) k5 k6 k7 sp (Z_to_bv 64 spa) (Z_to_bv 64 AN) (Z_to_bv 64 adx) k12 k13 k14 k15 k16 k17
                             (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) (Z_to_bv 64 ac) (Z_to_bv 64 arr) (Z_to_bv 64 arp) (Z_to_bv 64 f) (Z_to_bv 64 ara) (Z_to_bv 64 arm)
                             (Z_to_bv 64 SHB) (Z_to_bv 64 AN) k28 k29 k30 k31)
                        F5 (Z_to_bv 64 2860376) fc5 None m5 (seg_rom bgbsegs))).
        { intros until fc5. intros EV5 LS5 RS5 HA5 NRO5 U5. subst REST.
          apply implA_from_evt. step. step.
    apply evt_done.
          eapply implA_bind.
          { eapply ((BN_RECP_CTX_set_walkA CSL CSLcopy CSLnb)) with (lo := lo) (OW := OW5) (LB := ((q1, f + 32, 256) :: (q2, f + 352, 64) :: LB)) (PL := PL) (EA := EA);
              [| | | reflexivity | exact HA5 | exact NRO5 | exact HRC | exact INQ2 | exact AL8 | reflexivity | reflexivity].
            - eapply cenv_preA; [exact EV5 | exact LS5 | clear - LOK CSset; lia | pose proof TOTAL_OK as H; unfold EXP_RECP_TOTAL, BN_NNMOD_COST, BN_DIV_FT_COST, BN_RECP_CTX_SET_COST in H |- *; clear - H MCP CMM0 U5; lia].
            - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EV5).
            - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_BN_mod_exp_recp_2ba378 CTX).
          }
          cbv beta. intros [uc5 lsc5] Σc5 msc5 PO.
          apply (bn_postA_cpost ((q1, f + 32, 256) :: (q2, f + 352, 64) :: LB) PL EA lo (bv_unsigned sp) spa TOTAL Σ1 ls OW) in PO; [| exact OK | exact (proj1 (proj2 EV5))].
          cbn [fst snd] in *.
          destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & Fc5 & fcc5 & mc5 & OWc5 & PLc5 & -> & CPc5 & (EPLc5 & ->)).
          subst PLc5. specialize (CPc5 eq_refl).
          destruct (cenv_postA ((q1, f + 32, 256) :: (q2, f + 352, 64) :: LB) PL EA lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls OW mV _ _ _ _ _ _ _ _ _ _ _ EV5 CPc5) as (EVc5 & LSc5).
          pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CPc5) as RSc5. clear CPc5.
          rewrite (ret_pc_even 2860384) by (clear; lia).
          pose proof (refs_stable_trans _ _ _ _ _ _ RS5 RSc5) as RS35.
          unfold MallocRep.wz. apply implA_from_evt.
          step. if_false.
      pose proof EVc5 as (_ & _ & STc5 & MIc5 & _ & _ & _ & _ & FRc5 & FSZc5 & _). cbn [app locs] in FRc5.
          step. rewrite ?(unsigned_lit (f + 32)) by (clear - G1 G3 C1 C2 C3; lia).

          assert (WS0' : nth_error ws0 (Z.to_nat 0) = Some (Z_to_bv 64 av0)) by exact WS0.
          pose proof (obj_arrA (q1, f + 32, 256) ((q2, f + 352, 64) :: LB) PL lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls OW mV _ _ _ _ _ _ ws0 EVc5 VB
                        ltac:(cbn [blk_size snd]; rewrite LEN0; reflexivity) ltac:(cbn [blk_addr blk_size fst snd]; intros xq Hxq; apply NFVP; clear - Hxq; lia)) as VA.
          cbn [blk_addr fst snd] in VA.
          let a := cur_mem_addr in pose proof (u64arr_read bgbsegs mc5 (f + 32) _ 0 _ a VA WS0' ltac:(clear; lia) ltac:(addr_tac)) as RD.
          step. clear RD VA.
          step. step. step. step.
    apply evt_done.
          eapply implA_bind.
          { eapply (BN_nnmod_walkA) with (lo := lo) (OW := OWc5) (LB := ((q1, f + 32, 256) :: (q2, f + 352, 64) :: LB)) (PL := PL) (EA := EA);
              [| | | reflexivity | exact (ref_at_stable _ _ _ _ PL _ _ RS35 HAv0) | exact (ref_at_stable _ _ _ _ PL _ _ RS35 HAac3) | exact (ref_at_stable _ _ _ _ PL _ _ RS35 HAmc3) | rewrite Ev0; apply hpl_pool | exact NROa | exact NROm | exact NBaP | exact HPCP | reflexivity | reflexivity | reflexivity | reflexivity].
            - eapply cenv_preA; [exact EVc5 | exact LSc5 | clear - LOK CSnnmod; lia | pose proof TOTAL_OK as H; unfold EXP_RECP_TOTAL, BN_NNMOD_COST, BN_DIV_FT_COST, BN_RECP_CTX_SET_COST in H |- *; clear - H MCP CMM0 U5; lia].
            - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EVc5).
            - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_BN_mod_exp_recp_2ba394 CTX).
          }
          cbv beta. intros [uc4 lsc4] Σc4 msc4 PO.
          apply (bn_postA_cpost ((q1, f + 32, 256) :: (q2, f + 352, 64) :: LB) PL EA lo (bv_unsigned sp) spa TOTAL Σ1 ls OW) in PO; [| exact OK | exact (proj1 (proj2 EVc5))].
          cbn [fst snd] in *.
          destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & Fc4 & fcc4 & mc4 & OWc4 & PLc4 & -> & CPc4 & (EPLc4 & ->)).
          subst PLc4. specialize (CPc4 eq_refl).
          destruct (cenv_postA ((q1, f + 32, 256) :: (q2, f + 352, 64) :: LB) PL EA lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls OW mV _ _ _ _ _ _ _ _ _ _ _ EVc5 CPc4) as (EVc4 & LSc4).
          pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CPc4) as RSc4. clear CPc4.
          rewrite (ret_pc_even 2860412) by (clear; lia).
          pose proof (refs_stable_trans _ _ _ _ _ _ RS35 RSc4) as RS34.
          unfold MallocRep.wz.

          apply implA_from_evt. step. if_false.
      pose proof EVc4 as (_ & _ & STc4 & MIc4 & _ & _ & _ & _ & FRc4 & FSZc4 & _). cbn [app locs] in FRc4.
          pose proof (obj_arrA (q1, f + 32, 256) ((q2, f + 352, 64) :: LB) PL lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls OW mV _ _ _ _ _ _ ws0 EVc4 VB
                        ltac:(cbn [blk_size snd]; rewrite LEN0; reflexivity) ltac:(cbn [blk_addr blk_size fst snd]; intros xq Hxq; apply NFVP; clear - Hxq; lia)) as VA.
          cbn [blk_addr fst snd] in VA.
          let a := cur_mem_addr in pose proof (u64arr_read bgbsegs mc4 (f + 32) _ 0 _ a VA WS0' ltac:(clear; lia) ltac:(addr_tac)) as RD.
          step. clear RD VA.
          step.
    eapply (is_zero_callA ((q1, f + 32, 256) :: (q2, f + 352, 64) :: LB) PL EA lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls OW mV LOFB16); [exact EVc4 | exact LSc4 | exact (ref_at_stable _ _ _ _ PL _ _ RS34 HAv0) | exact NROv0 |].
        intros mZ y0Z y1Z y2Z y4Z y5Z y6Z y7Z y8Z y9Z y10Z y11Z y12Z y13Z y14Z EVZ LSZ.
          rewrite (ret_pc_even 2860424) by (clear; lia).
          unfold is_zero_pure. destruct (Nat.eqb_spec (bn_top (getbn uc3 lsc4)) 0) as [TZ|TNZ]; cbn [Z.b2z].
          {
            step. if_false. step. step.
            unfold BN_zero, bbind, bget, bset. cbn [bind ret tree_ops tbind fst snd].
            eapply (ExpBodyKitF.zero_callA ((q1, f + 32, 256) :: (q2, f + 352, 64) :: LB) PL EA lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls OW mV LOFB16); [exact EVZ | exact LSZ | exact (ref_at_stable _ _ _ _ PL _ _ (refs_stable_trans _ _ _ _ _ _ RS03 RS34) HArP) | exact (hpl_wref _ _ WRrP) |].
            intros mY z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 lsY EVY LSY.
            rewrite (ret_pc_even 2860436) by (clear; lia).
      pose proof EVY as (_ & _ & STY & MIY & _ & _ & _ & _ & FRY & FSZY & _). cbn [app locs] in FRY.
            step. step. step. step.
            apply evt_done. eapply exit_tail; [exact EVY | reflexivity | exact LSY | pose proof TOTAL_OK as H; unfold EXP_RECP_TOTAL, BN_NNMOD_COST, BN_DIV_FT_COST, BN_RECP_CTX_SET_COST in H |- *; clear - H MCP CMM0 U5; lia | exact AXB]. }

          step. if_true.
          assert (BC : bits * CMM <= 32768 * CMM) by (apply Z.mul_le_mono_nonneg_r; [exact CMM0 | clear - BITSR; lia]).
          apply evt_done. cbv beta.
          eapply (L_nonzeroA mV _ _ _ _ _ ws0 bits uc2 uc3 ad av0 di vi w0 w1 w2 w3 w8 w9);
            [exact EVZ | exact LSZ | exact AXB | exact VB | exact LEN0 | exact WS0
            | exact (ref_at_stable _ _ _ _ PL _ _ RS34 HAdc3) | exact Ed | exact (ref_at_stable _ _ _ _ PL _ _ RS34 HAv0) | exact Ev0 | exact AvR | exact BITSR
            | pose proof TOTAL_OK as H; unfold EXP_RECP_TOTAL, BN_NNMOD_COST, BN_DIV_FT_COST, BN_RECP_CTX_SET_COST in H |- *; clear - H MCP CMM0 BC U5; lia]. }
        destruct (bn_neg (getbn rm lsc3)) eqn:NEG; cbn [Z.b2z].
        -
          step. if_false.
          step. step. step.
    apply evt_done.
          apply implA_tbind_assoc. eapply implA_bind.
          { eapply (BN_copy_walkA) with (lo := lo) (OW := OWc3) (LB := ((q1, f + 32, 256) :: (q2, f + 352, 64) :: LB)) (PL := PL) (EA := EA);
              [| | | reflexivity | exact HAdc3 | exact HAmc3 | rewrite Ed; apply wref_pool | exact NROm | reflexivity | reflexivity].
            - eapply cenv_preA; [exact EVR | exact LSW | clear - LOK CScopy; lia | pose proof TOTAL_OK as H; unfold EXP_RECP_TOTAL, BN_NNMOD_COST, BN_DIV_FT_COST in H |- *; clear - H MCP CMM0; lia].
            - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EVR).
            - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_BN_mod_exp_recp_2ba314 CTX).
          }
          cbv beta. intros [uc6 lsc6] Σc6 msc6 PO.
          apply (bn_postA_cpost ((q1, f + 32, 256) :: (q2, f + 352, 64) :: LB) PL EA lo (bv_unsigned sp) spa TOTAL Σ1 ls OW) in PO; [| exact OK | exact (proj1 (proj2 EVR))].
          cbn [fst snd] in *.
          destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & Fc6 & fcc6 & mc6 & OWc6 & PLc6 & -> & CPc6 & (EPLc6 & -> & INCLc6)).
          subst PLc6. specialize (CPc6 eq_refl).
          destruct (cenv_postA ((q1, f + 32, 256) :: (q2, f + 352, 64) :: LB) PL EA lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls OW mV _ _ _ _ _ _ _ _ _ _ _ EVR CPc6) as (EVc6 & LSc6).
          pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CPc6) as RSc6. clear CPc6.
          rewrite (ret_pc_even 2860284) by (clear; lia).
          unfold MallocRep.wz. apply implA_from_evt.
          step. if_cases KZ2; rewrite ?unsigned_lit in KZ2 by (clear - AdR; lia); zify_cond KZ2; [exfalso; clear - KZ2 AdR; lia| clear KZ2].
          pose proof (ref_at_stable _ _ _ _ PL _ _ RSc6 HAdc3) as HAd6.
      pose proof EVc6 as (_ & _ & STc6 & MIc6 & _ & _ & _ & _ & FRc6 & FSZc6 & _). cbn [app locs] in FRc6.
          step.
          destruct (cenv_struct_openA ((q1, f + 32, 256) :: (q2, f + 352, 64) :: LB) PL EA lo (bv_unsigned sp) spa s0 ra ras TOTAL Σ1 ls OW mV LOFB16 _ _ _ _ _ _ uc2 ad EVc6 LSc6 HAd6 ltac:(rewrite Ed; apply wref_pool))
            as (Dd & BNd & OKd & ACCd & ALd & Ad0' & SEPd & OFSd & STd & MId & CLOSEd).
          unfold BnRepDefs.bn_cells in BNd. unfold SHLO, SHHI in OFSd.
          assert (AdT : 0 <= ad /\ ad + 24 <= 140737488355328) by (clear - SEPd FBSP SPT' Ad0'; lia).
          pose proof (munch_refl [(ad, ad + 24)]%Z mc6) as MUd. pose proof (wmono_refl bgbsegs mc6) as WMd.
          hide_ors. ub. unhide.
          step. step. step. shl_with ACCd ALd. chk0.
          step.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m7 end.
          set (bd := getbn uc2 lsc6) in *.
          assert (BNd' : rw_cells bgbsegs m7 ad (BnRepDefs.bn_cells Dd (bn_with_neg bd false))) by (unfold BnRepDefs.bn_cells, bn_with_neg; cbn [bn_d bn_top bn_buf bn_neg bn_flags bn_dmax Z.b2z length]; exact BNd).
          assert (OKd' : bg_ok (bn_with_neg bd false)) by (destruct OKd as (O1 & O2 & O3 & O4); unfold bg_ok, bn_with_neg, bn_dmax in *; cbn [bn_buf bn_top bn_flags]; repeat split; assumption).
          destruct (CLOSEd m7 (bn_with_neg bd false) MUd WMd BNd' eq_refl eq_refl OKd' STd MId) as (EV7 & LS7).
          clear CLOSEd BNd BNd' MUd WMd STd MId ACCd.
      pose proof EV7 as (_ & _ & ST7 & MI7 & _ & _ & _ & _ & FR7 & FSZ7 & _). cbn [app locs] in FR7.
          step. step.
          apply evt_done. cbv beta. cbn [fst snd].
          eapply (SETK uc2 ad _ _ _ m7 _);
            [exact EV7 | exact LS7 | eapply refs_stable_trans; [exact RSc6|]; intros PL' k a' H; apply ref_at_setbn; exact H
            | apply ref_at_setbn; exact HAd6 | exact NROd | clear - MCP; lia].
        -
          step. if_true.
          step. step.
          apply evt_done.
          eapply (SETK rm arm _ _ _ mV _);
            [exact EVR | exact LSW | apply refs_stable_refl | exact HAmc3 | exact NROm | clear - MCP; lia].
      Qed.

    End Scope.
  End Fixed.
End Proofs.
End Body.

Section Top.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).

  Variables (CS CSL CMM : Z).
  Hypothesis CSstart : BN_CTX_START_STACK <= CS.
  Hypothesis CSget : BN_CTX_GET_STACK <= CS.
  Hypothesis CSend : BN_CTX_END_STACK <= CS.
  Hypothesis CSnnmod : BN_NNMOD_STACK <= CS.
  Hypothesis CSsetw : BN_SET_WORD_STACK <= CS.
  Hypothesis CSnb : BN_NUM_BITS_STACK <= CS.
  Hypothesis CScopy : BN_COPY_STACK <= CS.
  Hypothesis CSLcopy : BN_COPY_STACK <= CSL.
  Hypothesis CSLnb : BN_NUM_BITS_STACK <= CSL.
  Hypothesis CSset : BN_RECP_CTX_SET_STACK CSL <= CS.
  Hypothesis CSinit : RECP_INIT_STACK <= CS.
  Hypothesis CSfree : RECP_FREE_STACK <= CS.
  Hypothesis CSrt : RT_STACK <= CS.
  Hypothesis CMM0 : 0 <= CMM.

  Hypothesis BN_mod_mul_reciprocal_walkA : forall (AR1 : ARun), forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts (@ar_RT AR1)) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
      (lo : Z) (ras : list Z) (rr rx ry : bnref) (ar ax ay an ac : Z) (qc : bptr) (q : bptr),
    bn_preA Σ ls m OW LB PL EA sp lo CS CMM ->
    fr_room 1 ls OW LB ->
    uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx 0x2bc4a8 (bv_unsigned ra :: ras) ->
    tp = wz TP_A -> ref_at ls OW PL rr ar -> ref_at ls OW PL rx ax -> ref_at ls OW PL ry ay -> hpl PL rr -> rx <> ROne -> ry <> ROne -> nbuf PL rx -> nbuf PL ry ->
    recp_at PL an -> In (q, an, 64) LB -> an mod 8 = 0 -> pl_ctx PL = Some (ac, qc) ->
    a0 = wz ar -> a1 = wz ax -> a2 = wz ay -> a3 = wz an -> a4 = wz ac ->
    implA (BN_mod_mul_reciprocal (tree_ops bptr) rr rx ry ls) Σ
      (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA CMM (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0x2bc4a8) fc None m (seg_rom bgbsegs)).

  Definition BN_MOD_EXP_RECP_STACK : Z := EXP_RECP_FRAME + CS.
  Definition BN_MOD_EXP_RECP_COST : Z := 1 + EXP_RECP_TOTAL CMM.

  Lemma BN_mod_exp_recp_walkA : exp_stmtAn_f BN_MOD_EXP_RECP BN_MOD_EXP_RECP_STACK BN_MOD_EXP_RECP_COST 2 (BN_mod_exp_recp (tree_ops bptr)) None.
  Proof.
    unfold exp_stmtAn_f, BN_MOD_EXP_RECP_STACK, BN_MOD_EXP_RECP_COST. intros until qc. intros PRE ROOM UW CTX -> HArr HAra HArp HArm HPr NRa NRp NRm NBa EC HFRESH -> -> -> -> -> _.
    destruct HFRESH as (HFN & HFNr & HFR & _ & _).
    assert (T0 : 0 <= EXP_RECP_TOTAL CMM) by (unfold EXP_RECP_TOTAL, BN_NNMOD_COST, BN_DIV_FT_COST, MC; clear - CMM0; lia).
    eapply (pro_exp_recp _ _) with (d := 1%nat); [exact PRE | exact ROOM | exact UW | reflexivity | clear - CSrt; lia | clear - T0; lia |].
    intros Σ1 m1 f spa q1 q2 g junk gj ra' u0 u1 u2 x10 x11 x12 x13 b4 b5 b6 b7 u3 u4 u5 u6 F' fc' j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 jv1 jv2 FE GSZ SAVJ FR FRV1 ACN1 FRV2 ACN2.
    pose proof FE as (HEAP1 & LS1 & FROK1 & ST1 & CEIL & LOK & SPT & SP16 & MI1 & CNT1 & CRED1 & FAL & NOFR1 & ROOM1 & SPA32 & SPAL & SPAH & CR1 & AXO & UW1 & FRESH & GEO).
    replace (1 + EXP_RECP_TOTAL CMM - 1) with (EXP_RECP_TOTAL CMM) in * by (clear; lia).
    pose proof (fr_env_cenv0 192 1%nat f 3 [(q1, f + 32, 256); (q2, f + 352, 64)] Σ ls m OW LB PL EA sp lo _ (EXP_RECP_TOTAL CMM) s0 ra ras spa Σ1 m1
                  ([CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3; CB 8 j4; CB 8 j5; CB 8 j6; CB 8 j7; CB 8 j8; CB 8 j9; C8 (Z_to_bv 64 f)] ++ [CB g junk])
                  FE ltac:(clear; lia) ltac:(unfold EXP_RECP_FRAME, RT_STACK in *; clear - CSrt; lia) FR
                  ltac:(cbn [app cells_size csize Nat.add]; clear - GSZ; lia)) as EV0.
    pose proof PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NOFR).
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS1) as (_ & PWF0 & _).
    eapply (@body_main (push AR f 3) UK BE CS CSL CMM CSstart CSget CSend CSnnmod CSsetw CSnb CScopy CSLcopy CSLnb CSset CSinit CSfree CMM0 (BN_mod_mul_reciprocal_walkA (push AR f 3))
              _ sp gp s0 ra Σ1 ls m1 OW LB PL EA lo spa f (EXP_RECP_TOTAL CMM) q1 q2 ras g junk rr ra_ rp rm arr ara arp arm ac qc);
      [ apply Z.le_refl
      | unfold EXP_RECP_FRAME in LOK; clear - LOK; lia
      | exact ROOM1
      | left; reflexivity
      | intros xq Hxq; apply (fr_no_placed PL LB f 3%nat xq NOFR FRESH); unfold fs_size; change (Z.shiftl 64 (Z.of_nat 3)) with 512; clear - Hxq; lia
      | exact CTX | exact EC | exact HFN | exact HFNr | exact HFR | exact PWF0 | exact HArr | exact HAra | exact HArp | exact HArm | exact HPr | exact NRa | exact NRp | exact NRm | exact NBa
      | | exact EV0 | exact LS1 ].
    intros Σk lsk mk OWk loc used mb x1 x5 x6 x7 x9 y10 y11 y12 y13 y14 y15 y16 y17 x20 x21 x22 rv x25 x26 x27 x28 x29 x30 x31 Fk fck EVk LSk USED AXB ->.
    eapply (epi_exp_recp tt _) with (mb := mb) (used := used) (gj := gj) (d := 1%nat) (m1 := m1) (Σ1 := Σ1);
      [exact PRE | replace (1 + EXP_RECP_TOTAL CMM - 1) with (EXP_RECP_TOTAL CMM) by (clear; lia); exact FE | unfold EXP_RECP_FRAME, RT_STACK in *; clear - CSrt; lia | exact GSZ | exact SAVJ
      | exact (ax_pres_trans _ _ _ _ _ _ AXO AXB) | replace (1 + EXP_RECP_TOTAL CMM - 1) with (EXP_RECP_TOTAL CMM) by (clear; lia); exact EVk | exact LSk | clear - USED; lia | split; reflexivity].
  Qed.
End Top.
