(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame.
From OSSVerify.Proofs.openssl.bignum.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.openssl.bignum.lib.BgMallocP Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BnModel BnTree BnInv BnBridge BgState BgInv BgLib BgWords BgArith BgMont.
From OSSVerify.Proofs.openssl.bignum.lib.BgP Require Import Layout Lib_iface Lib_kit F_memset.
From OSSVerify.Proofs.openssl.bignum.lib.BgP Require F_fwritex.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnArith BnMem BnTac BnTacX.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnP Require Import BnHeap W_small W_small2.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnP2 Require Import W_small3.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnP Require BnRep BnLeaves.
From OSSVerify.Proofs.openssl.bignum.lib.BgRep Require Import BgRepDefs BgRep BgLayer BgIface.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnR Require Import BgLeaves W_div_tail.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnR Require CtxKit.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnR Require W_ctx W_ctx_get W_ctx_end W_copy W_bndiv.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnR2 Require W_set_word W_sub_word W_set_bit W_shift W_mod_inverse InvClosed.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnE Require Import ExpKit ExpKitArr MontSetKit.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnE Require W_mont.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnR2 Require Import InvKit PlaceTmod.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.openssl.bignum.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Ltac the_mi := lazymatch goal with H : mem_inv bgpsegs _ |- _ => exact H end.
Ltac to_implM :=
  lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
    lazymatch E with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.

Local Notation ops := (tree_ops bptr).
Local Notation ST := (bstate bptr).
Local Notation BMu := (BM (M := btree bptr) (ptr := bptr)).

Definition ms_exit : BMu unit :=
  bbind ops (BN_CTX_end ops) (fun _ =>
  bbind ops (bget ops RTmod) (fun tm =>
  if (match bn_d tm with Some _ => true | None => false end) then bunr ops else
  bset ops RTmod (bn_nil 0))).

Definition ms_fix : BMu unit :=
  bbind ops (bget ops RMontRR) (fun rr =>
  bbind ops (bget ops RMontN) (fun n =>
  if (bn_dmax rr <? bn_top n)%nat then bunr ops else
  bbind ops (bset ops RMontRR (mkBN (bn_d rr) (splice (bn_buf rr) (bn_top rr) (repeat 0 (bn_top n - bn_top rr))) (bn_top n)
                                 (bn_neg rr) (bn_flags rr))) (fun _ =>
  ms_exit))).

Definition ms_rr (ri : Z) : BMu unit :=
  bbind ops (BN_zero ops RMontRR) (fun _ =>
  bbind ops (bgetst ops) (fun st =>
  if negb (st_ri st =? ri) then bunr ops else
  bbind ops (BN_set_bit ops RMontRR (ri * 2)) (fun _ =>
  bbind ops (BN_mod ops RMontRR RMontRR RMontN) (fun _ =>
  ms_fix)))).

Definition ms_n0 (rRi : bnref) (ri : Z) : BMu unit :=
  bbind ops (BN_div ops (Some rRi) None rRi RTmod) (fun _ =>
  bbind ops (bget ops rRi) (fun x =>
  let n0 := if (0 <? bn_top x)%nat then nth 0 (bn_buf x) 0 else 0 in
  bbind ops (bbind ops (bgetst ops) (fun st => bsetmont ops (st_ri st) n0)) (fun _ =>
  ms_rr ri))).

Definition ms_sub (rRi : bnref) (ri : Z) : BMu unit :=
  bbind ops (BN_lshift ops rRi rRi 64) (fun _ =>
  bbind ops (bget ops rRi) (fun x =>
  bbind ops (if negb (is_zero_pure x) then (if lval (firstn (bn_top x) (bn_buf x)) <? 1 then bunr ops else BN_sub_word ops rRi 1)
             else BN_set_word ops rRi BN_MASK2) (fun _ =>
  ms_n0 rRi ri))).

Definition ms_inv (rRi : bnref) (ri : Z) : BMu unit :=
  bbind ops (bget ops RTmod) (fun tm =>
  bbind ops (if is_one_pure tm then BN_zero ops rRi else BN_mod_inverse ops rRi RMontRR RTmod) (fun _ =>
  ms_sub rRi ri)).

Definition ms_mid (rmod rRi : bnref) : BMu unit :=
  bbind ops (BN_copy ops RMontN rmod) (fun _ =>
  bbind ops (bbind ops (bget ops RMontN) (fun n => bset ops RMontN (bn_with_neg n false))) (fun _ =>
  bbind ops (BN_num_bits ops rmod) (fun nb =>
  let ri := (nb + 63) / 64 * 64 in
  bbind ops (bbind ops (bgetst ops) (fun st => bsetmont ops ri (st_n0 st))) (fun _ =>
  bbind ops (BN_zero ops RMontRR) (fun _ =>
  bbind ops (BN_set_bit ops RMontRR 64) (fun _ =>
  bbind ops (bget ops rmod) (fun m =>
  if (bn_top m =? 0)%nat then bunr ops else
  let b0 := nth 0 (bn_buf m) 0 in
  bbind ops (bset ops RTmod (mkBN None [b0; 0] (if b0 =? 0 then 0%nat else 1%nat) false 0)) (fun _ =>
  ms_inv rRi ri)))))))).

Definition ms_all (rmod : bnref) : BMu unit :=
  bbind ops (bget ops rmod) (fun m =>
  if is_zero_pure m then bunr ops else
  bbind ops (BN_CTX_start ops) (fun _ =>
  bbind ops (BN_CTX_get ops) (fun rRi =>
  ms_mid rmod rRi))).

Lemma BN_MONT_CTX_set_eq : forall rmod, BN_MONT_CTX_set ops rmod = ms_all rmod.
Proof. reflexivity. Qed.

Lemma bbind_getst : forall {B} (f : ST -> BMu B) (bsK : ST), bbind ops (bgetst ops) f bsK = f bsK bsK.
Proof. reflexivity. Qed.
Lemma bbind_zero : forall {C : Type} r (K : unit -> BMu C) (bsK : ST),
  bbind ops (BN_zero ops r) K bsK = K tt (setbn r (bn_zero_pure (getbn r bsK)) bsK).
Proof. reflexivity. Qed.
Lemma bbind_getst_setmont : forall {C : Type} (fri fn0 : ST -> Z) (K : unit -> BMu C) (bsK : ST),
  bbind ops (bbind ops (bgetst ops) (fun st => bsetmont ops (fri st) (fn0 st))) K bsK = K tt (set_mont (fri bsK) (fn0 bsK) bsK).
Proof. reflexivity. Qed.

Lemma nth_error_wlimbs0 : forall (l : list Z) i, (i < length l)%nat -> nth_error (wlimbs l) i = Some (Z_to_bv 64 (nth i l 0)).
Proof. intros l i H. unfold wlimbs. rewrite nth_error_map. rewrite (nth_error_nth' l 0 H). reflexivity. Qed.

Lemma splice_nil : forall (l : list Z) off, splice l off [] = l.
Proof. intros l off. unfold splice. cbn [length app]. rewrite Nat.add_0_r. apply firstn_skipn. Qed.

Lemma memset_len : forall t nt, 0 <= t -> t < nt -> nt <= 512 ->
  Z.shiftr (Z.land (Z.shiftl (Z.land (nt + Z.lxor t 18446744073709551615) 18446744073709551615) 32) 18446744073709551615) 29 + 8 = 8 * (nt - t).
Proof.
  intros t nt T0 TN N5.
  rewrite zb_lxor_ones by lia.
  change 18446744073709551615 with (Z.ones 64). rewrite !Z.land_ones by lia.
  replace (nt + (Z.ones 64 - t)) with ((nt - t - 1) + 1 * 2^64) by (change (Z.ones 64) with (2^64 - 1); lia).
  rewrite Z.mod_add by lia. rewrite (Z.mod_small (nt - t - 1)) by lia.
  rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.mod_small by lia. rewrite Z.shiftr_div_pow2 by lia.
  replace ((nt - t - 1) * 2 ^ 32) with ((nt - t - 1) * 8 * 2 ^ 29) by lia. rewrite Z.div_mul by lia. lia.
Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition BN_MONT_CTX_SET : Z := 0xf7700.

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.
  Variable CS : Z.
  Hypothesis CS96 : 96 <= CS.
  Hypothesis STK_START : W_ctx.BN_CTX_START_STACK <= CS.
  Hypothesis STK_GET : W_ctx_get.BN_CTX_GET_STACK <= CS.
  Hypothesis STK_END : W_ctx_end.BN_CTX_END_STACK <= CS.
  Hypothesis STK_COPY : W_copy.BN_COPY_STACK <= CS.
  Hypothesis STK_SETBIT : W_set_bit.BN_SET_BIT_STACK <= CS.
  Hypothesis STK_INV : InvClosed.INV_STACK <= CS.
  Hypothesis STK_LSH : W_shift.BN_LSHIFT_W_STACK <= CS.
  Hypothesis STK_SETW : W_set_word.BN_SET_WORD_STACK <= CS.
  Hypothesis STK_SUBW : W_sub_word.BN_SUB_WORD_STACK <= CS.
  Hypothesis STK_DIV : W_bndiv.BN_DIV_TOP_STACK <= CS.
  Definition BN_MONT_CTX_SET_STACK : Z := 96 + CS.

  Local Tactic Notation "apw" uconstr(L) := first [eapply (L HM HF) | eapply (L HM) | eapply (L HF) | eapply L].

  Section Body.
    Variables (ra gp sp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
    Variables (lo B : Z) (s : PState) (bs : bstate bptr) (OW LB : list block) (m : mem) (PL0 : placement) (EA : BnRep.err_addrs).
    Variables (rd : bnref) (ad am ac : Z) (qm qc : bptr).
    Hypothesis CEIL : alloc_ceiling <= lo.
    Hypothesis GLO' : GLOBALS_TOP <= lo.
    Hypothesis LO : lo <= bv_unsigned sp - (96 + CS).
    Hypothesis SPB : bv_unsigned sp <= B.
    Hypothesis B63 : B < 2^63.
    Hypothesis FROK0 : frames_ok PL0 (bv_unsigned sp) B.
    Hypothesis HPC0 : pl_ctx PL0 = Some (ac, qc).
    Hypothesis HPM0 : pl_mont PL0 = Some (am, qm).
    Hypothesis HFT : pl_bn PL0 RTmod = None.
    Hypothesis PWF0 : pl_wf PL0.
    Hypothesis NROd : rd <> ROne.
    Hypothesis NTd : rd <> RTmod.

    Notation SPv := (bv_unsigned sp).
    Notation FB := (bv_unsigned sp + -96).
    Notation PL := (pl_place_tmod PL0 (FB + 16) FB).

    Lemma SPR2 : SPv < 2 ^ 64.
    Proof using. pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR. clear - SPR. lia. Qed.
    Lemma FBlo : lo <= FB. Proof using LO CS96. clear - LO CS96. lia. Qed.
    Lemma FBsp : FB <= SPv. Proof using. clear. lia. Qed.
    Lemma FB40 : FB + 40 <= SPv. Proof using. clear. lia. Qed.
    Lemma FBFB : FB <= FB. Proof using. clear. lia. Qed.
    Lemma FBB : FB <= B. Proof using SPB. clear - SPB. lia. Qed.
    Lemma FBR : FB < 2 ^ 64. Proof using. pose proof SPR2 as H. clear - H. lia. Qed.
    Lemma LOF : lo <= FB - CS. Proof using LO. clear - LO. lia. Qed.
    Lemma ESPF : bv_unsigned (Z_to_bv 64 FB) = FB.
    Proof using CEIL LO CS96. pose proof SPR2 as H. apply unsigned_lit. clear - H CEIL LO CS96. lia. Qed.
    Lemma FROKP : frames_ok PL FB B.
    Proof using CEIL LO CS96 SPB FROK0. exact (FROKT PL0 lo B SPv FB CEIL FBlo FB40 SPB FROK0). Qed.
    Lemma HPC : pl_ctx PL = Some (ac, qc). Proof using HPC0. exact HPC0. Qed.
    Lemma HPM : pl_mont PL = Some (am, qm). Proof using HPM0. exact HPM0. Qed.

    Definition saved : list cell := [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

    Definition FINALQ : unit * ST -> PState -> machine_state -> Prop :=
      bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL0 EA
              (fun (_ : unit) (_ : ST) (_ : list block) (PL' : placement) (a0' : word) => PL' = PL0 /\ a0' = wz 1).

    Notation KENV := (kenv LB PL0 lo B SPv FB s bs OW m).

    Local Ltac hres := let H := fresh "HRES" in intros ? ? ? ? ? H; hnf in H; exact (proj1 H).
    Local Ltac retpc n := replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

    Section Placed.
      Variables (stP : PState) (bsP : ST) (OWP : list block) (mP : mem) (frP : list cell) (tmP : BN).
      Hypothesis ENVP : KENV frP stP bsP mP OWP.
      Hypothesis SAVP : rw_cells bgpsegs mP (FB + 40) saved.
      Variables (rRi : bnref) (aRi : Z) (ri : Z).
      Hypothesis HRiP : exists i, rRi = RPool i.
      Hypothesis RIR : 0 <= ri <= 32832.

      Notation bsP' := (setbn RTmod tmP bsP).
      Notation KENVT := (kenv LB PL lo B FB FB stP bsP' OWP mP).
      Notation KCALL := (kcall LB PL EA lo B FB FB stP bsP' OWP mP CEIL GLO' FBlo FBFB FBB B63 FBR FROKP CS LOF).
      Notation KZERO := (k_is_zero LB PL EA lo B FB FB stP bsP' OWP mP CEIL GLO' FBlo FBFB FBB B63 FBR FROKP CS CS96 LOF).
      Notation KONE := (k_is_one LB PL EA lo B FB FB stP bsP' OWP mP CEIL GLO' FBlo FBFB FBB B63 FBR FROKP CS CS96 LOF).

      Notation BMS rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 t3 t4 t5 t6 pc mem :=
        (MS (mkR rax (Z_to_bv 64 FB) gp (Z_to_bv 64 RATP) t0 t1 t2 sp (Z_to_bv 64 ac) a0 a1 a2 a3 a4 a5 a6 a7
                 x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 pc) fc None mem (seg_rom bgpsegs)).

      Lemma L_exit : forall stK bsK mK OWK
          (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 x20 x21 t3 t4 t5 t6 : word),
        KENVT [] stK bsK mK OWK -> lib_state bsK mK OWK PL EA ->
        implM bgpsegs (interp (embed (ms_exit bsK))) stK FINALQ
          (BMS rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 1) x19 x20 x21 t3 t4 t5 t6 0xf7948 mK).
      Proof.
        intros until t6. intros ENVK LSK.
        pose proof SPR2 as SPR. pose proof ESPF as ESP. pose proof LO as LO'. pose proof GLO' as GLO2. unfold GLOBALS_TOP in GLO2.
        unfold ms_exit, MallocRep.wz.
        unfold implM. iprefix. zstep. zstep. ihere. to_implM.
        eapply KCALL; [exact ENVK | exact LSK
          | intros errv PRE; apw W_ctx_end.BN_CTX_end_walk; [exact (bn_pre_le _ _ _ _ _ _ _ _ _ _ _ _ _ PRE STK_END) | reflexivity | exact HPC | reflexivity]
          | hres |].
        intros u st' bs' m' OW' ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV' LS' RS' _. clear ENVK LSK.
        retpc 1014096.
        rewrite bbind_get.
        destruct (bn_d (getbn RTmod bs')) as [qd|] eqn:ED.
        { unfold bunr. cbn [unreachable tree_ops embed interp]. apply implM_interp_unr. }
        unfold bset. cbn [ret tree_ops embed interp]. apply implM_interp_ret.

        destruct (kenvT_unplace LB PL0 EA lo B SPv FB s bs OW m CEIL GLO' FBlo FB40 FROK0 HFT frP saved stP bsP bsP' mP OWP st' bs' m' OW'
                    ENVP (refs_stable_setbn _ _ _ _) SAVP ltac:(cbn; clear; lia) ENV' LS' PWF0 ED) as (ENVF & LSF).
        clear ENV' LS'.
        pose proof (kenv_final LB PL0 lo B SPv FB s bs OW m _ _ _ _ _ ENVF) as (F1 & F2 & STF & (errvF & F4) & F5 & F6 & F7 & F8 & F9 & FRF).
        apply bk_rw_cells_app in FRF. destruct FRF as (FR40 & FRS).
        change (Z.of_nat (cells_size (CB 16 (u64s (wlimbs (bn_buf (getbn RTmod bs')))) :: bn_cells FB (getbn RTmod bs')))) with 40 in FRS.
        unfold saved in FRS. unfold bn_cells in FR40.
        replace (FB + 40) with (bv_unsigned sp + -56) in FRS by (clear; lia).
        zstep. do 7 zstep.
        release_frame FR40 STF (bv_unsigned sp + -56). release_frame FRS STF (bv_unsigned sp). do 2 zstep.
        apply evt_done. unfold FINALQ, bn_post. do 15 eexists. exists m', OW', PL0, errvF.
        split; [reflexivity|]. cbn [fst snd].
        split; [exact F1|]. split; [exact LSF|]. split; [exact F2|]. split; [exact STF|]. split; [exact F4|]. split; [exact F5|].
        split; [exact F6|]. split; [exact F7|]. split; [exact F8|]. split; [exact F9|]. split; reflexivity.
      Qed.

      Lemma L_fix : forall stK bsK mK OWK
          (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 x20 x21 t3 t4 t5 t6 : word),
        KENVT [] stK bsK mK OWK -> lib_state bsK mK OWK PL EA ->
        implM bgpsegs (interp (embed (ms_fix bsK))) stK FINALQ
          (BMS rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 am) x19 x20 x21 t3 t4 t5 t6 0xf7900 mK).
      Proof.
        intros until t6. intros ENVK LSK.
        pose proof SPR2 as SPR. pose proof ESPF as ESP. pose proof LO as LO'. pose proof GLO' as GLO2. unfold GLOBALS_TOP in GLO2.
        pose proof FBlo as FBL.
        pose proof (W_mont.ref_at_montRR bsK OWK PL am qm HPM) as HARR.
        pose proof (W_mont.ref_at_montN bsK OWK PL am qm HPM) as HAN.
        unfold ms_fix. rewrite !bbind_get.
        set (rr := getbn RMontRR bsK) in *. set (n := getbn RMontN bsK) in *.
        destruct (Nat.ltb_spec (bn_dmax rr) (bn_top n)) as [LT|GE].
        { unfold bunr. cbn [unreachable tree_ops embed interp]. apply implM_interp_unr. }
        rewrite bbind_set.

        destruct (kenv_open LB PL EA lo B FB FB stP bsP' OWP mP CEIL FROKP _ _ _ _ _ RMontN (am + 24) ENVK LSK HAN W_mont.RMontN_not_one)
          as (DN & BNN & _ & (_ & OKN2 & OKN3 & _) & AN0 & SEPAN & _ & _).
        fold n in BNN, OKN2, OKN3.
        destruct (kenv_open LB PL EA lo B FB FB stP bsP' OWP mP CEIL FROKP _ _ _ _ _ RMontRR am ENVK LSK HARR W_mont.RMontRR_not_one)
          as (DR & BNR & UR & (OKR1 & OKR2 & OKR3 & OKR4) & AR0 & SEPAR & SEPDR & SEPR).
        fold rr in BNR, UR, OKR1, OKR2, OKR3, OKR4, SEPDR, SEPR.
        unfold bn_cells, MallocRep.wz in BNN, BNR. unfold BG_DMAX in OKN3, OKR3.
        unfold implM. iprefix.
        zstep. zstep.
        rewrite (sx32_small (Z.of_nat (bn_top rr))) by (clear - OKR2 OKR3; unfold bn_dmax in *; lia).
        rewrite (sx32_small (Z.of_nat (bn_top n))) by (clear - OKN2 OKN3; unfold bn_dmax in *; lia).
        zstep. if_cases KT; zify_cond KT; rewrite !signed_small in KT by (clear - OKR2 OKR3 OKN2 OKN3; unfold bn_dmax in *; lia).
        -
          assert (EBUF : splice (bn_buf rr) (bn_top rr) (repeat 0 (bn_top n - bn_top rr)) = bn_buf rr).
          { replace (bn_top n - bn_top rr)%nat with 0%nat by (clear - KT; lia). apply splice_nil. }
          rewrite EBUF.
          destruct (kenv_struct_store LB PL EA lo B FB FB stP bsP' OWP mP CEIL GLO' FBlo FBFB FBB B63 FBR FROKP _ _ _ _ _ RMontRR am ENVK LSK HARR W_mont.RMontRR_not_one)
            as (DR' & BNR' & _ & _ & _ & _ & _ & CLOSE).
          fold rr in BNR', CLOSE. unfold bn_cells, MallocRep.wz in BNR'.
          clear BNR UR BNN.
          pose proof ENVK as (_ & _ & STK & _ & MIK & _).
          pose proof (munch_refl [(am, am + 24)]%Z mK) as MU. pose proof (wmono_refl bgpsegs mK) as WM.
          zstep.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
          destruct (CLOSE m1 (mkBN (bn_d rr) (bn_buf rr) (bn_top n) (bn_neg rr) (bn_flags rr)) MU WM) as (ENV1 & LS1);
            [ exact BNR' | reflexivity | reflexivity
            | unfold bg_ok, bn_dmax, BG_DMAX in *; cbn [bn_buf bn_top bn_flags]; split; [exact OKR1|]; split; [exact GE|]; split; [exact OKR3| exact OKR4]
            | exact STK | exact MIK |].
          clear BNR' MU WM STK MIK CLOSE.
          zstep. zstep.
          ihere. to_implM.
          eapply L_exit; [exact ENV1 | exact LS1].
        -
          clear BNR UR SEPAR SEPDR SEPR AR0 DR.
          assert (HDr : (0 < bn_dmax rr)%nat) by (clear - KT GE; lia).
          destruct (kenv_read LB PL EA lo B FB FB stP bsP' OWP mP CEIL FROKP _ _ _ _ _ RMontRR am ENVK LSK HARR (W_mont.wref_montRR PL am qm HPM) HDr)
            as (Dr & pr & Edr & Hinr & BNr & Ur & _ & (Ar0 & ArS & Ar63 & ArI) & (Dr0 & DrS & DrI) & SEPr & _).
          fold rr in Edr, Hinr, BNr, Ur, DrS, DrI, SEPr.
          pose proof (SEPr RMontRR am HARR) as SQR. clear SEPr.
          destruct (kenv_hole1 LB PL EA lo B FB FB stP bsP' OWP mP CEIL GLO' FBlo FBFB FBB B63 FBR FROKP _ _ _ _ _ RMontRR am Dr pr 0 ENVK LSK HARR W_mont.RMontRR_not_one
                      Edr Hinr ltac:(clear; lia) ltac:(clear - FBL; lia)) as (_ & CLOSE).
          fold rr in CLOSE.
          pose proof ENVK as (_ & _ & ST & (errv2 & ERR) & MI & _ & _ & _ & _ & FR & _).
          unfold LX_ERRNO, RATP in ERR. change (3061704 - 164) with 3061540 in ERR.
          unfold bn_cells, MallocRep.wz in BNr.
          pose proof (munch_refl (fpw1 FB 0 am Dr (bn_dmax rr)) mK) as MU. pose proof (wmono_refl bgpsegs mK) as WM. unfold fpw1 in MU.
          clear BNN.
          set (t := bn_top rr) in *. set (nt := bn_top n) in *.
          assert (LBr : length (bn_buf rr) = bn_dmax rr) by reflexivity.

          apply (limbarr_split bgpsegs mK Dr (bn_buf rr) t ltac:(rewrite LBr; exact OKR2)) in Ur. destruct Ur as [Ulo Ur].
          apply (limbarr_split bgpsegs mK (Dr + 8 * Z.of_nat t) (skipn t (bn_buf rr)) (nt - t) ltac:(rewrite length_skipn, LBr; clear - GE KT; lia)) in Ur.
          destruct Ur as [Umid Uhi].
          apply limbarr_CB in Umid. rewrite firstn_length_le in Umid by (rewrite length_skipn, LBr; clear - GE KT; lia).
          apply limbarr_CB in Ulo. rewrite firstn_length_le in Ulo by (rewrite LBr; exact OKR2).
          apply limbarr_CB in Uhi. rewrite !length_skipn, LBr in Uhi.
          replace (Dr + 8 * Z.of_nat t + 8 * Z.of_nat (nt - t)) with (Dr + 8 * Z.of_nat nt) in Uhi by (clear - KT; lia).
          replace (bn_dmax rr - t - (nt - t))%nat with (bn_dmax rr - nt)%nat in Uhi by (clear - KT GE; lia).
          zstep. do 7 zstep.
          rewrite (memset_len (Z.of_nat t) (Z.of_nat nt)) by (clear - KT GE OKR3; unfold bn_dmax in *; lia).
          replace (Z.shiftl (Z.of_nat t) 3) with (8 * Z.of_nat t) by (rewrite Z.shiftl_mul_pow2 by lia; clear; lia).
          replace (8 * (Z.of_nat nt - Z.of_nat t)) with (8 * Z.of_nat (nt - t)) by (clear - KT; lia).
          do 3 zstep.
          apply hide_intro in FR. apply hide_intro in ERR.
          eapply evt_cut.
          { eapply (memset_callZ _ (Z_to_bv 64 FB)) with (D := Dr + 8 * Z.of_nat t) (C := 0) (N := 8 * Z.of_nat (nt - t));
              [ replace (Z.to_nat (8 * Z.of_nat (nt - t))) with (8 * (nt - t))%nat by (clear; lia); exact Umid
              | exact MI | clear - Dr0; lia | clear - KT GE OKR3; unfold bn_dmax in *; lia | clear - Dr0 DrS KT GE SPR FBL; unfold bn_dmax in *; lia | clear; lia ]. }
          clear Umid.
          post_call bgpsegs mK.
          lazymatch goal with P : rw_cells bgpsegs _ (Dr + 8 * Z.of_nat t) [CB _ (repeat _ _)] |- _ => rename P into PZ end.
          change (0 mod 256) with 0 in PZ. replace (Z.to_nat (8 * Z.of_nat (nt - t))) with (8 * (nt - t))%nat in PZ by (clear; lia).
          rewrite <- lbytes_repeat0 in PZ.
          apply CB_u64arr in PZ. apply CB_u64arr in Ulo. apply CB_u64arr in Uhi.
          assert (LSP : length (splice (bn_buf rr) t (repeat 0 (nt - t))) = length (bn_buf rr)).
          { apply splice_length. rewrite repeat_length, LBr. clear - KT GE. lia. }
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
          assert (U3 : u64arr bgpsegs m3 Dr (wlimbs (splice (bn_buf rr) t (repeat 0 (nt - t))))).
          { unfold splice. rewrite repeat_length. apply limbarr_app. split; [exact Ulo|].
            rewrite firstn_length_le by (rewrite LBr; exact OKR2). apply limbarr_app. split; [exact PZ|].
            rewrite repeat_length. replace (Dr + 8 * Z.of_nat t + 8 * Z.of_nat (nt - t)) with (Dr + 8 * Z.of_nat nt) by (clear - KT; lia).
            rewrite skipn_skipn in Uhi. replace (t + (nt - t))%nat with (nt - t + t)%nat by (clear; lia). exact Uhi. }
          clear Ulo Uhi PZ.
          assert (LU3 : Z.of_nat (length (wlimbs (splice (bn_buf rr) t (repeat 0 (nt - t))))) = Z.of_nat (bn_dmax rr)) by (rewrite wlimbs_len, LSP, LBr; reflexivity).
          zstep.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
          apply hide_elim in FR. apply hide_elim in ERR.
          eapply (rw_cells_transport bgpsegs _ mK m4) in FR; [| exact MU | exact WM | cbn [disjoint_from cells_size]; split; [right; clear; lia|]; split; [clear - ArS FBL; lia|]; split; [right; clear - DrS FBL; lia| exact I]].
          eapply (rw_cells_transport bgpsegs _ mK m4) in ERR; [| exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; split; [left; clear - FBL GLO2; lia|]; split; [clear - ArI; lia|]; split; [clear - DrI; lia| exact I]].
          set (b2 := mkBN (bn_d rr) (splice (bn_buf rr) t (repeat 0 (nt - t))) nt (bn_neg rr) (bn_flags rr)) in *.
          destruct (CLOSE m4 b2 errv2 MU WM) as (ENV4 & LS4).
          { change (bn_cells Dr b2) with [C8 (wz Dr); C4 (wz (Z.of_nat nt)); C4 (wz (Z.of_nat (length (splice (bn_buf rr) t (repeat 0 (nt - t))))));
                                          C4 (wz (Z.b2z (bn_neg rr))); C4 (wz (bn_flags rr))].
            rewrite LSP, LBr. exact BNr. }
          { exact U3. } { reflexivity. } { exact LSP. }
          { unfold bg_ok, BG_DMAX. change (bn_dmax b2) with (length (splice (bn_buf rr) t (repeat 0 (nt - t)))). cbn [b2 bn_buf bn_top bn_flags]. rewrite LSP, LBr.
            split; [apply splice_limbs; [exact OKR1| apply limbs_repeat; exact limb_0]|]. split; [exact GE|]. split; [exact OKR3| exact OKR4]. }
          { exact ST. } { the_mi. } { exact FR. } { unfold LX_ERRNO, RATP. exact ERR. }
          zstep. zstep.
          ihere. to_implM.
          eapply L_exit; [exact ENV4 | exact LS4].
      Qed.

      Lemma L_rr : forall stK bsK mK OWK
          (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x20 x21 t3 t4 t5 t6 : word),
        KENVT [] stK bsK mK OWK -> lib_state bsK mK OWK PL EA ->
        implM bgpsegs (interp (embed (ms_rr ri bsK))) stK FINALQ
          (BMS rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 am) (Z_to_bv 64 (am + 24)) x20 x21 t3 t4 t5 t6 0xf78c8 mK).
      Proof.
        intros until t6. intros ENVK LSK.
        pose proof SPR2 as SPR. pose proof ESPF as ESP. pose proof LO as LO'. pose proof GLO' as GLO2. unfold GLOBALS_TOP in GLO2.
        pose proof FBlo as FBL. pose proof LOF as LOFF.
        unfold ms_rr. rewrite bbind_zero. rewrite bbind_getst.
        change (st_ri (setbn RMontRR (bn_zero_pure (getbn RMontRR bsK)) bsK)) with (st_ri bsK).
        destruct (Z.eqb_spec (st_ri bsK) ri) as [ERI|NE]; cbn [negb].
        2:{ unfold bunr. cbn [unreachable tree_ops embed interp]. apply implM_interp_unr. }
        unfold implM. iprefix. zstep. zstep.
        eapply (zero_call LB PL EA lo B FB FB stP bsP' OWP mP CEIL GLO' FBlo FBFB FBB B63 FBR FROKP);
          [clear - LOFF CS96; lia | reflexivity | exact ENVK | exact LSK | exact (W_mont.ref_at_montRR bsK OWK PL am qm HPM) | exact (W_mont.wref_montRR PL am qm HPM) |].
        intros m1 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV1 LS1. clear ENVK LSK.
        retpc 1013968.
        set (bs1 := setbn RMontRR (bn_zero_pure (getbn RMontRR bsK)) bsK) in *.

        pose proof (lib_state_mont_cells _ _ _ _ _ _ _ am qm LS1 HPM) as MC. unfold mont_cells, MallocRep.wz in MC.
        change (st_ri bs1) with (st_ri bsK) in MC. rewrite ERI in MC.
        zstep. rewrite (sx32_small ri) by (clear - RIR; lia).
        zstep.
        replace (Z.shiftl ri 1) with (ri * 2) by (rewrite Z.shiftl_mul_pow2 by lia; clear; lia).
        rewrite (bn_swrap32_small (ri * 2)) by (clear - RIR; lia).
        clear MC.
        zstep. zstep.
        pose proof (W_mont.ref_at_montRR bs1 OWK PL am qm HPM) as HARR1.
        ihere. to_implM.
        eapply KCALL; [exact ENV1 | exact LS1
          | intros errv PRE; apw W_set_bit.BN_set_bit_walk; [exact (bn_pre_le _ _ _ _ _ _ _ _ _ _ _ _ _ PRE STK_SETBIT) | reflexivity | exact HARR1
                                                         | exact (W_mont.wref_montRR PL am qm HPM) | reflexivity | reflexivity | clear - RIR; lia]
          | hres |].
        intros u2 st2 bs2 m2 OW2 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV2 LS2 RS2 RES2. hnf in RES2. destruct RES2 as (_ & -> & _). unfold MallocRep.wz.
        clear ENV1 LS1 HARR1.
        retpc 1013984.
        unfold implM. iprefix. zstep. if_false. do 5 zstep. zstep.
        ihere. to_implM.
        unfold BN_mod.
        eapply KCALL; [exact ENV2 | exact LS2
          | intros errv PRE; eapply (W_bndiv.BN_div_walk HM HF) with (dv := None) (rm := Some RMontRR);
              [exact (bn_pre_le _ _ _ _ _ _ _ _ _ _ _ _ _ PRE STK_DIV) | reflexivity | exact HPC | reflexivity
              | exact (W_mont.ref_at_montRR bs2 OW2 PL am qm HPM) | exact (W_mont.ref_at_montRR bs2 OW2 PL am qm HPM) | exact (W_mont.ref_at_montN bs2 OW2 PL am qm HPM)
              | intros d X; discriminate X | intros r X; injection X as <-; exact (hpl_mont PL RMontRR am qm eq_refl HPM)
              | exact W_mont.RMontRR_not_one | exact W_mont.RMontN_not_one
              | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity]
          | hres |].
        intros u3 st3 bs3 m3 OW3 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV3 LS3 RS3 RES3. hnf in RES3. destruct RES3 as (_ & ->). unfold MallocRep.wz.
        clear ENV2 LS2.
        retpc 1014012.
        unfold implM. iprefix. zstep. if_false.
        ihere. to_implM.
        eapply L_fix; [exact ENV3 | exact LS3].
      Qed.

      Lemma L_n0 : forall stK bsK mK OWK
          (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x21 t3 t4 t5 t6 : word),
        KENVT [] stK bsK mK OWK -> lib_state bsK mK OWK PL EA -> ref_at bsK OWK PL rRi aRi ->
        implM bgpsegs (interp (embed (ms_n0 rRi ri bsK))) stK FINALQ
          (BMS rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 am) (Z_to_bv 64 (am + 24)) (Z_to_bv 64 aRi) x21 t3 t4 t5 t6 0xf788c mK).
      Proof.
        intros until t6. intros ENVK LSK HARi.
        pose proof SPR2 as SPR. pose proof ESPF as ESP. pose proof LO as LO'. pose proof GLO' as GLO2. unfold GLOBALS_TOP in GLO2.
        pose proof FBlo as FBL. pose proof LOF as LOFF.
        destruct HRiP as (iRi & ERi).
        assert (NRORi : rRi <> ROne) by (rewrite ERi; unfold RPool, ROne, NFIX; lia).
        unfold ms_n0.
        unfold implM. iprefix. do 5 zstep. zstep.
        replace (Z_to_bv 64 (bv_unsigned sp + -80)) with (Z_to_bv 64 (FB + 16)) by (f_equal; clear; lia).
        ihere. to_implM.
        eapply KCALL; [exact ENVK | exact LSK
          | intros errv PRE; eapply (W_bndiv.BN_div_walk HM HF) with (dv := Some rRi) (rm := None);
              [exact (bn_pre_le _ _ _ _ _ _ _ _ _ _ _ _ _ PRE STK_DIV) | reflexivity | exact HPC | exact HARi | reflexivity
              | exact HARi | exact (ref_at_place_tmod_same bsK OWK PL0 (FB + 16) FB)
              | intros d X; injection X as <-; rewrite ERi; apply wref_pool | intros r X; discriminate X
              | exact NRORi | unfold RTmod, ROne; clear; lia
              | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity]
          | hres |].
        intros u1 st1 bs1 m1 OW1 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV1 LS1 RS1 RES1. hnf in RES1. destruct RES1 as (_ & ->). unfold MallocRep.wz.
        pose proof (ref_at_stable _ _ _ _ PL _ _ RS1 HARi) as HARi1.
        clear ENVK LSK HARi RS1.
        retpc 1013924.
        rewrite bbind_get. cbv zeta. rewrite (bbind_getst_setmont (fun st => st_ri st)).
        set (x := getbn rRi bs1) in *.
        set (n0 := if (0 <? bn_top x)%nat then nth 0 (bn_buf x) 0 else 0) in *.

        assert (TAIL : forall (z0 z1 z2 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 rax' : word),
                  implM bgpsegs (interp (embed (ms_rr ri (set_mont (st_ri bs1) n0 bs1)))) st1 FINALQ
                    (BMS rax' z0 z1 z2 (Z_to_bv 64 n0) z4 z5 z6 z7 z8 z9 z10 (Z_to_bv 64 am) (Z_to_bv 64 (am + 24)) (Z_to_bv 64 aRi) x21 z11 z12 z13 z14 0xf78c0 m1)).
        { intros.
          pose proof (lib_state_mont_cells _ _ _ _ _ _ _ am qm LS1 HPM) as MC. unfold mont_cells, MallocRep.wz in MC.
          pose proof ENV1 as (HEAP1 & _ & ST1 & (errv1 & ERR1) & MI1 & _ & _ & _ & _ & FR1 & _).
          pose proof (lib_state_h_parts _ _ _ _ _ _ LS1) as PARTS1.
          pose proof PARTS1 as (_ & _ & _ & (_ & _ & PM) & _). rewrite HPM in PM.
          pose proof (RH_range _ _ _ _ _ _ _ HEAP1 PM) as (M0 & _ & _ & MC1 & MI2). unfold MONT_CTX_SZ in MC1, MI2.
          unfold LX_ERRNO, RATP in ERR1. change (3061704 - 164) with 3061540 in ERR1.
          pose proof (munch_refl [(am + 72, am + MONT_CTX_SZ)]%Z m1) as MU. pose proof (wmono_refl bgpsegs m1) as WM. unfold MONT_CTX_SZ in MU.
          unfold implM. iprefix.
          zstep. zstep.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
          assert (LS2 : lib_state (set_mont (st_ri bs1) n0 bs1) m2 OW1 PL EA).
          { eapply (lib_state_set_mont _ LB FB B false [] bs1 m1 m2 OW1 PL EA am qm (st_ri bs1) n0);
              [exact HEAP1| exact LS1| exact FROKP| exact HPM| exact MU| exact WM| exact MC]. }
          assert (ENV2 : KENVT [] st1 (set_mont (st_ri bs1) n0 bs1) m2 OW1).
          { apply kenv_set_mont.
            assert (HWL : Forall (w_lib bs1 OW1 PL lo FB) [(am + 72, am + 96)]).
            { constructor; [|constructor]. right; left. exists (qm, am, MONT_CTX_SZ). split; [exact PM|]. cbn [blk_addr blk_size fst snd]. unfold MONT_CTX_SZ. clear. lia. }
            exact (kenv_silent LB PL EA lo B FB FB stP bsP' OWP mP CEIL GLO' FBlo FBFB FBB FROKP [] [] st1 bs1 m1 m2 OW1 _ errv1
                     ENV1 PARTS1 MU WM HWL ST1 ERR1 MI1 FR1 ltac:(cbn; clear; lia)). }
          ihere. to_implM.
          eapply L_rr; [exact ENV2 | exact LS2]. }
        destruct (kenv_open LB PL EA lo B FB FB stP bsP' OWP mP CEIL FROKP _ _ _ _ _ rRi aRi ENV1 LS1 HARi1 NRORi)
          as (Di & BNi & Ui & (OKi1 & OKi2 & OKi3 & OKi4) & Ai0 & SEPAi & SEPDi & SEPi).
        fold x in BNi, Ui, OKi1, OKi2, OKi3, OKi4, SEPDi, SEPi.
        unfold bn_cells, MallocRep.wz in BNi. unfold BG_DMAX in OKi3.
        assert (AiR : 0 < aRi < 2^64).
        { pose proof (ref_at_hrange _ _ _ _ _ _ _ _ _ (proj1 ENV1) (lib_state_h_parts _ _ _ _ _ _ LS1) HARi1 ltac:(rewrite ERi; apply hpl_pool)) as (R0 & RC & _).
          clear - R0 RC CEIL FBL SPR. lia. }
        unfold implM. iprefix.
        zstep. if_false.
        zstep. rewrite (sx32_small (Z.of_nat (bn_top x))) by (clear - OKi2 OKi3; unfold bn_dmax in *; lia).
        zstep.
        if_cases KT.
        -
          assert (EN : n0 = 0).
          { unfold n0. destruct (Nat.ltb_spec 0 (bn_top x)) as [H|H]; [exfalso| reflexivity].
            zify_cond KT. apply Bool.andb_false_iff in KT. destruct KT as [KT|KT]; [apply Z.ltb_ge in KT; clear - H KT; lia|].
            apply Z.ltb_ge in KT. clear - KT OKi2 OKi3. unfold bn_dmax in *. lia. }
          clear KT.
          zstep.
          rewrite <- EN.
          ihere. to_implM. apply TAIL.
        -
          assert (TOP1 : (0 < bn_top x)%nat).
          { destruct (Nat.ltb_spec 0 (bn_top x)) as [H|H]; [exact H| exfalso]. replace (bn_top x) with 0%nat in KT by (clear - H; lia). vm_compute in KT. discriminate KT. }
          clear KT.
          assert (EN : n0 = nth 0 (bn_buf x) 0).
          { unfold n0. destruct (Nat.ltb_spec 0 (bn_top x)) as [H|H]; [reflexivity| exfalso; clear - H TOP1; lia]. }
          zstep.
          assert (NTH0 : nth_error (wlimbs (bn_buf x)) (Z.to_nat 0) = Some (Z_to_bv 64 (nth 0 (bn_buf x) 0))).
          { apply nth_error_wlimbs0. clear - OKi2 TOP1. unfold bn_dmax in OKi2. lia. }
          let a := cur_mem_addr in pose proof (u64arr_read bgpsegs m1 Di _ 0 _ a Ui NTH0 ltac:(lia) ltac:(addr_tac)) as RD.
          zstep. clear RD NTH0.
          zstep.
          rewrite <- EN.
          ihere. to_implM. apply TAIL.
      Qed.

      Lemma L_sub : forall stK bsK mK OWK
          (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x21 t3 t4 t5 t6 : word),
        KENVT [] stK bsK mK OWK -> lib_state bsK mK OWK PL EA -> ref_at bsK OWK PL rRi aRi ->
        implM bgpsegs (interp (embed (ms_sub rRi ri bsK))) stK FINALQ
          (BMS rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 am) (Z_to_bv 64 (am + 24)) (Z_to_bv 64 aRi) x21 t3 t4 t5 t6 0xf7848 mK).
      Proof.
        intros until t6. intros ENVK LSK HARi.
        pose proof SPR2 as SPR. pose proof ESPF as ESP. pose proof LO as LO'. pose proof GLO' as GLO2. unfold GLOBALS_TOP in GLO2.
        pose proof FBlo as FBL. pose proof LOF as LOFF.
        pose proof HRiP as (iRi & ERi).
        assert (NRORi : rRi <> ROne) by (rewrite ERi; unfold RPool, ROne, NFIX; lia).
        assert (HPRi : hpl PL rRi) by (rewrite ERi; apply hpl_pool).
        unfold ms_sub.
        unfold implM. iprefix. do 3 zstep. zstep.
        ihere. to_implM.
        eapply KCALL; [exact ENVK | exact LSK
          | intros errv PRE; apw W_shift.BN_lshift_walk; [exact (bn_pre_le _ _ _ _ _ _ _ _ _ _ _ _ _ PRE STK_LSH) | reflexivity | exact HARi | exact HPRi | exact HARi | exact NRORi
                                                       | reflexivity | reflexivity | reflexivity | clear; lia]
          | hres |].
        intros u1 st1 bs1 m1 OW1 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV1 LS1 RS1 RES1. hnf in RES1. destruct RES1 as (_ & -> & _). unfold MallocRep.wz.
        pose proof (ref_at_stable _ _ _ _ PL _ _ RS1 HARi) as HARi1.
        clear ENVK LSK HARi RS1.
        retpc 1013848.
        rewrite bbind_get. set (x := getbn rRi bs1) in *.
        unfold implM. iprefix. zstep. if_false. zstep. zstep.
        eapply KZERO; [exact ENV1 | exact LS1 | exact HARi1 | exact NRORi |].
        intros m2 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV2 LS2. clear ENV1 LS1.
        retpc 1013860.
        fold x.
        destruct (is_zero_pure x) eqn:EZ; cbn [negb Z.b2z].
        -
          zstep. if_false. zstep. zstep. zstep.
          replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 BN_MASK2) by (apply bv_eq; vm_compute; reflexivity).
          ihere. to_implM.
          eapply KCALL; [exact ENV2 | exact LS2
            | intros errv PRE; apw W_set_word.BN_set_word_walk; [exact (bn_pre_le _ _ _ _ _ _ _ _ _ _ _ _ _ PRE STK_SETW) | reflexivity | exact HARi1 | exact (hpl_wref PL rRi HPRi)
                                                              | reflexivity | reflexivity | unfold BN_MASK2, BW; clear; lia]
            | hres |].
          intros u3 st3 bs3 m3 OW3 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV3 LS3 RS3 RES3. hnf in RES3. destruct RES3 as (_ & -> & _). unfold MallocRep.wz.
          pose proof (ref_at_stable _ _ _ _ PL _ _ RS3 HARi1) as HARi3.
          clear ENV2 LS2.
          retpc 1013876.
          unfold implM. iprefix. zstep. if_true.
          ihere. to_implM.
          eapply L_n0; [exact ENV3 | exact LS3 | exact HARi3].
        -
          destruct (Z.ltb_spec (lval (firstn (bn_top x) (bn_buf x))) 1) as [LT1|GE1].
          { ihere. to_implM. unfold bbind, bunr. cbn [bind unreachable tree_ops tbind embed interp]. apply implM_interp_unr. }
          zstep. if_true. zstep. zstep. zstep.
          ihere. to_implM.
          eapply KCALL; [exact ENV2 | exact LS2
            | intros errv PRE; apw W_sub_word.BN_sub_word_walk; [exact (bn_pre_le _ _ _ _ _ _ _ _ _ _ _ _ _ PRE STK_SUBW) | reflexivity | exact HARi1 | exact (hpl_wref PL rRi HPRi)
                                                              | reflexivity | reflexivity | clear; lia | exact GE1]
            | hres |].
          intros u3 st3 bs3 m3 OW3 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV3 LS3 RS3 RES3. hnf in RES3. destruct RES3 as (_ & -> & _). unfold MallocRep.wz.
          pose proof (ref_at_stable _ _ _ _ PL _ _ RS3 HARi1) as HARi3.
          clear ENV2 LS2.
          retpc 1013896.
          unfold implM. iprefix. zstep. if_false.
          ihere. to_implM.
          eapply L_n0; [exact ENV3 | exact LS3 | exact HARi3].
      Qed.

      Lemma L_inv : forall stK bsK mK OWK
          (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x21 t3 t4 t5 t6 : word),
        KENVT [] stK bsK mK OWK -> lib_state bsK mK OWK PL EA -> ref_at bsK OWK PL rRi aRi ->
        implM bgpsegs (interp (embed (ms_inv rRi ri bsK))) stK FINALQ
          (BMS rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 am) (Z_to_bv 64 (am + 24)) (Z_to_bv 64 aRi) x21 t3 t4 t5 t6 0xf7818 mK).
      Proof.
        intros until t6. intros ENVK LSK HARi.
        pose proof SPR2 as SPR. pose proof ESPF as ESP. pose proof LO as LO'. pose proof GLO' as GLO2. unfold GLOBALS_TOP in GLO2.
        pose proof FBlo as FBL. pose proof LOF as LOFF.
        pose proof HRiP as (iRi & ERi).
        assert (NRORi : rRi <> ROne) by (rewrite ERi; unfold RPool, ROne, NFIX; lia).
        assert (HPRi : hpl PL rRi) by (rewrite ERi; apply hpl_pool).
        assert (NROT : RTmod <> ROne) by (unfold RTmod, ROne; lia).
        assert (AiR : 0 < aRi < 2^64).
        { pose proof (ref_at_hrange _ _ _ _ _ _ _ _ _ (proj1 ENVK) (lib_state_h_parts _ _ _ _ _ _ LSK) HARi HPRi) as (R0 & RC & _).
          clear - R0 RC CEIL FBL SPR. lia. }
        unfold ms_inv. rewrite bbind_get.
        unfold implM. iprefix. zstep. zstep.
        replace (Z_to_bv 64 (bv_unsigned sp + -80)) with (Z_to_bv 64 (FB + 16)) by (f_equal; clear; lia).
        eapply KONE; [exact ENVK | exact LSK | exact (ref_at_place_tmod_same bsK OWK PL0 (FB + 16) FB) | exact NROT |].
        intros m1 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV1 LS1. clear ENVK LSK.
        retpc 1013792.
        destruct (is_one_pure (getbn RTmod bsK)) eqn:EONE; cbn [Z.b2z].
        -
          rewrite bbind_zero.
          zstep. if_false. zstep. zstep.
          eapply (zero_call LB PL EA lo B FB FB stP bsP' OWP mP CEIL GLO' FBlo FBFB FBB B63 FBR FROKP);
            [clear - LOFF CS96; lia | reflexivity | exact ENV1 | exact LS1 | exact HARi | exact (hpl_wref PL rRi HPRi) |].
          intros m2 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV2 LS2. clear ENV1 LS1.
          retpc 1013804.
          zstep.
          ihere. to_implM.
          eapply L_sub; [exact ENV2 | exact LS2 | apply ref_at_setbn; exact HARi].
        -
          zstep. if_true. do 4 zstep. zstep.
          replace (Z_to_bv 64 (bv_unsigned sp + -80)) with (Z_to_bv 64 (FB + 16)) by (f_equal; clear; lia).
          ihere. to_implM.
          eapply KCALL; [exact ENV1 | exact LS1
            | intros errv PRE; eapply (InvClosed.BN_mod_inverse_closed HM HF);
                [exact (bn_pre_le _ _ _ _ _ _ _ _ _ _ _ _ _ PRE STK_INV) | reflexivity | exact HARi | exact HPRi
                | exact (W_mont.ref_at_montRR bsK OWK PL am qm HPM) | exact W_mont.RMontRR_not_one
                | exact (ref_at_place_tmod_same bsK OWK PL0 (FB + 16) FB) | exact NROT | exact HPC
                | reflexivity | reflexivity | reflexivity | reflexivity]
            | hres |].
          intros u2 st2 bs2 m2 OW2 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV2 LS2 RS2 RES2. hnf in RES2. destruct RES2 as (_ & ->). unfold MallocRep.wz.
          pose proof (ref_at_stable _ _ _ _ PL _ _ RS2 HARi) as HARi2.
          clear ENV1 LS1.
          retpc 1013828.
          unfold implM. iprefix.
          zstep. if_cases KR; rewrite ?unsigned_lit in KR by (clear - AiR; lia); zify_cond KR. { exfalso. clear - KR AiR. lia. }
          ihere. to_implM.
          eapply L_sub; [exact ENV2 | exact LS2 | exact HARi2].
      Qed.
    End Placed.
  End Body.
End Proofs.
End WithCeiling0.
