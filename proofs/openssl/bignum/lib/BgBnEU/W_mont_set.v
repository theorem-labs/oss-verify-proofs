(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BnModel BnTree BnInv BnBridge BgState BgInv BgLib BgWords BgArith BgMont.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Import Layout Lib_iface Lib_kit F_memset.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require F_fwritex.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnArith BnMem BnTac BnTacX.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require Import BnHeap W_small W_small2.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU2 Require Import W_small3.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require BnRep BnLeaves.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgRepU Require Import BgRepDefs BgRep BgLayer BgIface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnRU Require Import BgLeaves W_div_tail.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnRU Require CtxKit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnRU Require W_ctx W_ctx_get W_ctx_end W_copy W_bndiv.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnRU2 Require W_set_word W_sub_word W_set_bit W_shift W_mod_inverse InvClosed.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnEU Require Import ExpKit ExpKitArr MontSetKit W_mont_set_b.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnEU Require W_mont W_recp_set.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnRU2 Require Import InvKit PlaceTmod.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgRepU Require Import BnUAlign.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnBoth Require Import UbKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Local Notation ops := (tree_ops bptr).
Local Notation ST := (bstate bptr).
Local Notation BMu := (BM (M := btree bptr) (ptr := bptr)).

Definition ms_a4 (rmod rRi : bnref) (ri : Z) : BMu unit :=
  bbind ops (bget ops rmod) (fun m =>
  if (bn_top m =? 0)%nat then bunr ops else
  let b0 := nth 0 (bn_buf m) 0 in
  bbind ops (bset ops RTmod (mkBN None [b0; 0] (if b0 =? 0 then 0%nat else 1%nat) false 0)) (fun _ =>
  ms_inv rRi ri)).

Definition ms_a3 (rmod rRi : bnref) : BMu unit :=
  bbind ops (BN_num_bits ops rmod) (fun nb =>
  let ri := (nb + 63) / 64 * 64 in
  bbind ops (bbind ops (bgetst ops) (fun st => bsetmont ops ri (st_n0 st))) (fun _ =>
  bbind ops (BN_zero ops RMontRR) (fun _ =>
  bbind ops (BN_set_bit ops RMontRR 64) (fun _ =>
  ms_a4 rmod rRi ri)))).

Definition ms_a2 (rmod rRi : bnref) : BMu unit :=
  bbind ops (bbind ops (bget ops RMontN) (fun n => bset ops RMontN (bn_with_neg n false))) (fun _ =>
  ms_a3 rmod rRi).

Lemma bbind_get_set0 : forall {C : Type} r (g : bignum bptr -> bignum bptr) (K : unit -> BMu C) (bsK : ST),
  bbind ops (bbind ops (bget ops r) (fun b => bset ops r (g b))) K bsK = K tt (setbn r (g (getbn r bsK)) bsK).
Proof. reflexivity. Qed.

Lemma bbind_num_bits : forall {C : Type} r (K : Z -> BMu C) (bsK : ST), bg_ok (getbn r bsK) ->
  bbind ops (BN_num_bits ops r) K bsK = K (num_bits_pure (getbn r bsK)) bsK.
Proof.
  intros C r K bsK (_ & _ & _ & FL). unfold bbind at 1. unfold BN_num_bits. rewrite bbind_get. unfold has_flag.
  assert (EL4 : Z.land (bn_flags (getbn r bsK)) BN_FLG_CONSTTIME = 0) by (destruct FL as [E|E]; rewrite E; reflexivity).
  rewrite EL4. reflexivity.
Qed.

Lemma land_m64_small : forall x, 0 <= x < 32832 -> Z.land x 18446744073709551552 = x / 64 * 64.
Proof.
  intros x Hx.
  replace x with (64 * (x / 64) + x mod 64) at 1 by (symmetry; apply Z.div_mod; lia).
  pose proof (Z.mod_pos_bound x 64 ltac:(lia)) as HM.
  pose proof (Z.div_pos x 64 ltac:(lia) ltac:(lia)) as HD.
  assert (HQ : x / 64 < 513) by (apply Z.div_lt_upper_bound; lia).
  set (q := x / 64) in *. set (r := x mod 64) in *.
  change 18446744073709551552 with (Z.shiftl (Z.ones 58) 6).
  replace (64 * q + r) with (Z.lor (Z.shiftl q 6) r).
  2:{ rewrite <- Z.lxor_lor. 2:{ apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0, Z.shiftl_spec by lia.
        destruct (Z.lt_ge_cases i 6) as [H6|H6]; [rewrite (Z.testbit_neg_r q (i - 6)) by lia; reflexivity|].
        rewrite (Z.bits_above_log2 r i); [apply andb_false_r| lia|]. destruct (Z.eq_dec r 0) as [->|NZ]; [cbn; lia|]. apply Z.log2_lt_pow2; [lia|].
        assert (2^6 <= 2^i) by (apply Z.pow_le_mono_r; lia). lia. }
      rewrite <- Z.add_nocarry_lxor. { rewrite Z.shiftl_mul_pow2 by lia. lia. }
      apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0, Z.shiftl_spec by lia.
      destruct (Z.lt_ge_cases i 6) as [H6|H6]; [rewrite (Z.testbit_neg_r q (i - 6)) by lia; reflexivity|].
      rewrite (Z.bits_above_log2 r i); [apply andb_false_r| lia|]. destruct (Z.eq_dec r 0) as [->|NZ]; [cbn; lia|]. apply Z.log2_lt_pow2; [lia|].
      assert (2^6 <= 2^i) by (apply Z.pow_le_mono_r; lia). lia. }
  rewrite Z.land_lor_distr_l.
  rewrite <- Z.shiftl_land.
  replace (Z.land q (Z.ones 58)) with q by (symmetry; rewrite Z.land_ones by lia; apply Z.mod_small; lia).
  replace (Z.land r (Z.shiftl (Z.ones 58) 6)) with 0.
  2:{ symmetry. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0, Z.shiftl_spec by lia.
      destruct (Z.lt_ge_cases i 6) as [H6|H6]; [rewrite (Z.testbit_neg_r (Z.ones 58) (i - 6)) by lia; apply andb_false_r|].
      rewrite (Z.bits_above_log2 r i); [reflexivity| lia|]. destruct (Z.eq_dec r 0) as [->|NZ]; [cbn; lia|]. apply Z.log2_lt_pow2; [lia|].
      assert (2^6 <= 2^i) by (apply Z.pow_le_mono_r; lia). lia. }
  rewrite Z.lor_0_r. rewrite Z.shiftl_mul_pow2 by lia. lia.
Qed.

Lemma ms_mid_eq : forall rmod rRi, ms_mid rmod rRi = bbind ops (BN_copy ops RMontN rmod) (fun _ => ms_a2 rmod rRi).
Proof. reflexivity. Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.
  Variable CS : Z.
  Hypothesis CS128 : 128 <= CS.
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

  Local Tactic Notation "apw" uconstr(L) := first [eapply (L HM HF) | eapply (L HM) | eapply (L HF) | eapply L].

  Section Body.
    Variables (ra gp sp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
    Variables (lo B : Z) (s : PState) (bs : bstate bptr) (OW LB : list block) (m : mem) (PL0 : placement) (EA : BgBnU.BnRep.err_addrs).
    Variables (rd : bnref) (ad am ac : Z) (qm qc : bptr).
    Hypothesis CEIL : alloc_ceiling <= lo.
    Hypothesis GLO' : GLOBALS_TOP <= lo.
    Hypothesis LO : lo <= bv_unsigned sp - (96 + CS).
    Hypothesis SPB : bv_unsigned sp <= B.
    Hypothesis B63 : B < 2^63.
    Hypothesis FROK0 : frames_ok PL0 (bv_unsigned sp) B.
    Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
    Hypothesis HPC0 : pl_ctx PL0 = Some (ac, qc).
    Hypothesis HPM0 : pl_mont PL0 = Some (am, qm).
    Hypothesis HFT : pl_bn PL0 RTmod = None.
    Hypothesis PWF0 : pl_wf PL0.
    Hypothesis NROd : rd <> ROne.
    Hypothesis NTd : rd <> RTmod.
    Hypothesis AMR : 0 < am /\ am + 96 <= alloc_ceiling.
    Hypothesis ADR : 0 < ad < 2^64.

    Notation SPv := (bv_unsigned sp).
    Notation FB := (bv_unsigned sp + -96).
    Notation PL := (pl_place_tmod PL0 (FB + 16) FB).

    Lemma SPR2 : SPv < 2 ^ 64.
    Proof using. pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR. clear - SPR. lia. Qed.
    Lemma FBlo : lo <= FB. Proof using LO CS128. clear - LO CS128. lia. Qed.
    Lemma FBsp : FB <= SPv. Proof using. clear. lia. Qed.
    Lemma FB40 : FB + 40 <= SPv. Proof using. clear. lia. Qed.
    Lemma LOF : lo <= FB - CS. Proof using LO. clear - LO. lia. Qed.
    Lemma ESPF : bv_unsigned (Z_to_bv 64 FB) = FB.
    Proof using CEIL LO CS128. pose proof SPR2 as H. apply unsigned_lit. clear - H CEIL LO CS128. lia. Qed.

    Notation saved := (W_mont_set_b.saved ra s0 s1 s2 s3 s4 s5).
    Notation FINALQ := (W_mont_set_b.FINALQ ra gp sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo B s bs OW LB m PL0 EA).

    Definition fr0 (j0 j1 js : list byte) : list cell := [CB 8 j0; CB 8 j1; CB 24 js] ++ saved.
    Definition fr1 (j0 j1 : list byte) : list cell := [CB 8 j0; CB 8 j1] ++ BgRepDefs.bn_cells 0 (bn_nil 0) ++ saved.
    Definition fr2 (j0 j1 : list byte) : list cell :=
      [CB 8 j0; CB 8 j1; C8 (Z_to_bv 64 FB); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 2); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ++ saved.

    Notation KENV := (kenv LB PL0 lo B SPv FB s bs OW m).
    Notation KCALL := (kcall LB PL0 EA lo B SPv FB s bs OW m CEIL GLO' FBlo FBsp SPB B63 SPR2 FROK0 CS LOF).
    Notation KZERO := (k_is_zero LB PL0 EA lo B SPv FB s bs OW m CEIL GLO' FBlo FBsp SPB B63 SPR2 FROK0 CS CS128 LOF).
    Notation KFLAGS := (k_get_flags LB PL0 EA lo B SPv FB s bs OW m CEIL GLO' FBlo FBsp SPB B63 SPR2 FROK0 CS CS128 LOF).
    Notation KBITS := (k_num_bits LB PL0 EA lo B SPv FB s bs OW m CEIL GLO' FBlo FBsp SPB B63 SPR2 FROK0 CS CS128 LOF).

    Local Ltac hres := let H := fresh "HRES" in intros ? ? ? ? ? H; hnf in H; exact (proj1 H).
    Local Ltac retpc n := replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

    Notation AMS rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 x20 t3 t4 t5 t6 pc mem :=
      (MS (mkR rax (Z_to_bv 64 FB) gp (Z_to_bv 64 RATP) t0 t1 t2 sp (Z_to_bv 64 ac) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 am) x19 x20 (Z_to_bv 64 ad) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 pc) fc None mem (seg_rom bgusegs)).

    Section Ri.
      Variables (rRi : bnref) (aRi : Z).
      Hypothesis HRiP : exists i, rRi = RPool i.

      Lemma L_A4 : forall ri j0 j1 stK bsK mK OWK
          (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
        0 <= ri <= 32832 ->
        KENV (fr2 j0 j1) stK bsK mK OWK -> lib_state bsK mK OWK PL0 EA -> ref_at bsK OWK PL0 rd ad -> ref_at bsK OWK PL0 rRi aRi ->
        implM bgusegs (interp (embed (ms_a4 rd rRi ri bsK))) stK FINALQ
          (AMS rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (am + 24)) (Z_to_bv 64 aRi) t3 t4 t5 t6 0x100654 mK).
      Proof.
        intros until t6. intros RIR ENVK LSK HAd HARi.
        pose proof SPR2 as SPR. pose proof ESPF as ESP. pose proof LO as LO'. pose proof GLO' as GLO2. unfold GLOBALS_TOP in GLO2.
        pose proof FBlo as FBL. pose proof LOF as LOFF.
        unfold ms_a4. rewrite bbind_get. set (bm := getbn rd bsK) in *.
        destruct (Nat.eqb_spec (bn_top bm) 0) as [E0|NE0].
        { unfold bunr. cbn [unreachable tree_ops embed interp]. apply implM_interp_unr. }
        cbv zeta. rewrite bbind_set.
        set (b0 := nth 0 (bn_buf bm) 0) in *.
        destruct (kenv_open_u LB PL0 EA lo B SPv FB s bs OW m CEIL FROK0 _ _ _ _ _ rd ad ENVK LSK HAd NROd)
          as (Dd & BNd & Ud & (OKd1 & OKd2 & OKd3 & OKd4) & Ad0 & SEPAd & SEPDd & SEPd & (_ & AD8) & UBDd).
        fold bm in BNd, Ud, OKd1, OKd2, OKd3, OKd4, SEPDd, SEPd, UBDd.
        unfold BgRepDefs.bn_cells, MallocRep.wz in BNd. unfold BG_DMAX in OKd3.
        assert (LB0 : 0 <= b0 < 2^64).
        { pose proof (limbs_nth (bn_buf bm) 0 OKd1) as H. fold b0 in H. unfold limb in H. rewrite BnArith.BW_lit in H. clear - H. lia. }
        pose proof ENVK as (HEAPK & _ & STK & (errvK & ERRK) & MIK & _ & _ & _ & _ & FRK & _).
        pose proof (lib_state_h_parts _ _ _ _ _ _ LSK) as PARTSK.
        pose proof (munch_refl [(FB, SPv)]%Z mK) as MU. pose proof (wmono_refl bgusegs mK) as WM.
        unfold LX_ERRNO, RATP in ERRK. change (3346328 - 164) with 3346164 in ERRK.
        unfold fr2, W_mont_set_b.saved in FRK. cbn [app] in FRK.
        destruct (UBDd ltac:(clear - NE0; lia)) as (DD0 & DD8).
        pose proof (u64arr_bound _ _ _ _ Ud) as BUd.
        assert (DDR : (0 < Dd < 18446744073709551616)%Z).
        { destruct BUd as [BU0 BU1]. change (2 ^ 64)%Z with 18446744073709551616%Z in BU1. rewrite wlimbs_len in BU1.
          split; [exact DD0|]. clear - BU1 NE0 OKd2. unfold bn_dmax in *. lia. }
        unfold implM. iprefix.
        ub. zstep. ub.
        assert (NTH0 : nth_error (wlimbs (bn_buf bm)) (Z.to_nat 0) = Some (Z_to_bv 64 b0)).
        { apply nth_error_wlimbs0. clear - OKd2 NE0. unfold bn_dmax in OKd2. lia. }
        let a := cur_mem_addr in pose proof (u64arr_read bgusegs mK Dd _ 0 _ a Ud NTH0 ltac:(lia) ltac:(addr_tac)) as RD.
        zstep. clear RD NTH0.
        clear BNd Ud.
        ub. zstep. ub. zstep. ub. zstep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.

        set (tm := mkBN (@None bptr) [b0; 0] (if b0 =? 0 then 0%nat else 1%nat) false 0) in *.
        replace (Z.b2z (0 <? b0)) with (Z.of_nat (if b0 =? 0 then 0%nat else 1%nat)) in FRK
          by (clear - LB0; destruct (Z.eqb_spec b0 0) as [E|E]; destruct (Z.ltb_spec 0 b0) as [H|H]; cbn; lia).
        change (rw_cells bgusegs m3 FB ([C8 (Z_to_bv 64 b0); C8 (Z_to_bv 64 0)] ++ BgRepDefs.bn_cells FB tm ++ saved)) in FRK.
        assert (ENV3 : KENV ([C8 (Z_to_bv 64 b0); C8 (Z_to_bv 64 0)] ++ BgRepDefs.bn_cells FB tm ++ saved) stK bsK m3 OWK).
        { eapply (kenv_silent LB PL0 EA lo B SPv FB s bs OW m CEIL GLO' FBlo FBsp SPB FROK0) with (W := [(FB, SPv)]) (errv' := errvK);
            [exact ENVK | exact PARTSK | exact MU | exact WM | constructor; [left; cbn [fst snd]; clear - FBL; lia | constructor]
            | exact STK | unfold LX_ERRNO, RATP; exact ERRK | exact MIK | exact FRK | cbn; clear; lia]. }
        assert (LS3 : lib_state bsK m3 OWK PL0 EA).
        { eapply (lib_state_frame stK LB SPv B [] bsK mK m3 OWK PL0 EA _ HEAPK LSK MU WM FROK0).
          constructor; [apply w_stack; cbn [fst snd]; clear - FBL CEIL; lia | constructor]. }
        assert (OKT : bg_ok tm).
        { unfold bg_ok, tm, bn_dmax, BG_DMAX. cbn [bn_buf bn_top bn_flags length].
          split; [constructor; [unfold limb; rewrite BnArith.BW_lit; clear - LB0; lia| constructor; [exact limb_0| constructor]]|].
          split; [destruct (b0 =? 0); clear; lia|]. split; [clear; lia| left; reflexivity]. }
        destruct (kenvT_place LB PL0 EA lo B SPv FB s bs OW m CEIL GLO' FBlo FB40 SPB FROK0 HFT saved stK bsK m3 OWK tm b0 0 ENV3 LS3
                    ltac:(clear - FBL CEIL; lia) ltac:(clear - SP16; Z.div_mod_to_equations; lia) eq_refl eq_refl OKT) as (ENVT & LST & SAVP & _).
        destruct HRiP as (iRi & ERi).
        ihere. to_implM.
        eapply (L_inv HM HF CS CS128 STK_END STK_SETBIT STK_INV STK_LSH STK_SETW STK_SUBW STK_DIV
                  ra gp sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo B s bs OW LB m PL0 EA rd am ac qm qc
                  CEIL GLO' LO SPB B63 FROK0 SP16 HPC0 HPM0 HFT PWF0 NROd NTd
                  stK bsK OWK m3 _ tm ENV3 SAVP rRi aRi ri (ex_intro _ iRi ERi) RIR);
          [exact ENVT | exact LST |].
        apply ref_at_setbn. apply ref_at_place_tmod; [rewrite ERi; unfold RPool, RTmod, NFIX; clear; lia| exact HARi].
      Qed.

      Lemma L_A3 : forall j0 j1 stK bsK mK OWK
          (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
        KENV (fr2 j0 j1) stK bsK mK OWK -> lib_state bsK mK OWK PL0 EA -> ref_at bsK OWK PL0 rd ad -> ref_at bsK OWK PL0 rRi aRi ->
        implM bgusegs (interp (embed (ms_a3 rd rRi bsK))) stK FINALQ
          (AMS rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (am + 24)) (Z_to_bv 64 aRi) t3 t4 t5 t6 0x1005fc mK).
      Proof.
        intros until t6. intros ENVK LSK HAd HARi.
        pose proof SPR2 as SPR. pose proof ESPF as ESP. pose proof LO as LO'. pose proof GLO' as GLO2. unfold GLOBALS_TOP in GLO2.
        pose proof FBlo as FBL. pose proof LOF as LOFF.
        destruct (kenv_open LB PL0 EA lo B SPv FB s bs OW m CEIL FROK0 _ _ _ _ _ rd ad ENVK LSK HAd NROd)
          as (Dd & _ & _ & OKd & _ & _ & _ & _).
        pose proof OKd as (OKd1 & OKd2 & OKd3 & OKd4).
        set (bm := getbn rd bsK) in *. unfold BG_DMAX in OKd3.
        assert (CTd : Z.land (bn_flags bm) 4 = 0) by (destruct OKd4 as [E|E]; rewrite E; reflexivity).
        pose proof (W_recp_set.nbits_range bm OKd1) as NBR.
        unfold ms_a3. rewrite (bbind_num_bits rd _ bsK OKd). fold bm. cbv zeta.
        set (nb := num_bits_pure bm) in *. set (ri := (nb + 63) / 64 * 64) in *.
        assert (RIR : 0 <= ri <= 32832).
        { unfold ri. clear - NBR OKd2 OKd3. unfold bn_dmax in *. pose proof (Z.div_pos (nb + 63) 64 ltac:(lia) ltac:(lia)).
          pose proof (Z.mul_div_le (nb + 63) 64 ltac:(lia)). lia. }
        rewrite (bbind_getst_setmont (fun _ => ri) (fun st => st_n0 st)). rewrite bbind_zero.
        unfold implM. iprefix. do 2 zstep. zstep.
        eapply KFLAGS; [exact ENVK | exact LSK | exact HAd | exact NROd | clear; lia |].
        intros m1 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV1 LS1. clear ENVK LSK.
        retpc 1050120. fold bm. rewrite CTd.
        zstep. if_true. zstep. zstep.
        eapply KBITS; [exact ENV1 | exact LS1 | exact HAd | exact NROd |].
        intros m2 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV2 LS2. clear ENV1 LS1.
        retpc 1050144. fold bm. fold nb.
        zstep.
        rewrite (bn_swrap32_small (nb + 63)) by (clear - NBR OKd2 OKd3; unfold bn_dmax in *; lia).
        ub.
        setreg 10%Z (Z_to_bv 64 ri) ltac:(f_equal; unfold ri; change 18446744073709551615%Z with (2^64 - 1)%Z;
          rewrite (zb_land_mask (Z.shiftl (nb + 63) 1) 64) by lia;
          rewrite Z.shiftl_mul_pow2 by lia;
          rewrite (Z.mod_small ((nb + 63) * 2^1)) by (clear - NBR OKd2 OKd3; unfold bn_dmax in *; lia);
          rewrite Z.shiftr_div_pow2 by lia;
          rewrite (Z.div_small ((nb + 63) * 2^1)) by (clear - NBR OKd2 OKd3; unfold bn_dmax in *; lia);
          rewrite Z.add_0_r, (zb_land_mask (nb + 63) 64) by lia;
          rewrite Z.mod_small by (clear - NBR OKd2 OKd3; unfold bn_dmax in *; lia);
          symmetry; apply land_m64_small; clear - NBR OKd2 OKd3; unfold bn_dmax in *; lia).

        pose proof (lib_state_mont_cells _ _ _ _ _ _ _ am qm LS2 HPM0) as MC. unfold mont_cells, MallocRep.wz in MC.
        pose proof ENV2 as (HEAP2 & _ & ST2 & (errv2 & ERR2) & MI2 & _ & _ & _ & _ & FR2 & _).
        pose proof (lib_state_h_parts _ _ _ _ _ _ LS2) as PARTS2.
        pose proof PARTS2 as (_ & _ & _ & (_ & _ & PM) & _). rewrite HPM0 in PM.
        pose proof (RH_range _ _ _ _ _ _ _ HEAP2 PM) as (M0 & _ & _ & MC1 & MIm). unfold MONT_CTX_SZ in MC1, MIm.
        unfold LX_ERRNO, RATP in ERR2. change (3346328 - 164) with 3346164 in ERR2.
        pose proof (munch_refl [(am + 72, am + MONT_CTX_SZ)]%Z m2) as MU. pose proof (wmono_refl bgusegs m2) as WM. unfold MONT_CTX_SZ in MU.
        zstep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
        assert (LS3 : lib_state (set_mont ri (st_n0 bsK) bsK) m3 OWK PL0 EA).
        { eapply (lib_state_set_mont _ LB SPv B false [] bsK m2 m3 OWK PL0 EA am qm ri (st_n0 bsK));
            [exact HEAP2| exact LS2| exact FROK0| exact HPM0| exact MU| exact WM| exact MC]. }
        assert (ENV3 : KENV (fr2 j0 j1) stK (set_mont ri (st_n0 bsK) bsK) m3 OWK).
        { apply kenv_set_mont.
          assert (HWL : Forall (w_lib bsK OWK PL0 lo SPv) [(am + 72, am + 96)]).
          { constructor; [|constructor]. right; left. exists (qm, am, MONT_CTX_SZ). split; [exact PM|]. cbn [blk_addr blk_size fst snd]. unfold MONT_CTX_SZ. clear. lia. }
          exact (kenv_silent LB PL0 EA lo B SPv FB s bs OW m CEIL GLO' FBlo FBsp SPB FROK0 _ _ stK bsK m2 m3 OWK _ errv2
                   ENV2 PARTS2 MU WM HWL ST2 ERR2 MI2 FR2 ltac:(cbn; clear; lia)). }
        clear MC MU WM ST2 ERR2 MI2 FR2 HEAP2 PARTS2 PM ENV2 LS2.
        set (bs3 := set_mont ri (st_n0 bsK) bsK) in *.

        zstep. zstep.
        eapply (zero_call LB PL0 EA lo B SPv FB s bs OW m CEIL GLO' FBlo FBsp SPB B63 SPR2 FROK0);
          [clear - LOFF CS128; lia | reflexivity | exact ENV3 | exact LS3 | exact (W_mont.ref_at_montRR bs3 OWK PL0 am qm HPM0) | exact (W_mont.wref_montRR PL0 am qm HPM0) |].
        intros m4 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV4 LS4. clear ENV3 LS3.
        retpc 1050180.
        set (bs4 := setbn RMontRR (bn_zero_pure (getbn RMontRR bs3)) bs3) in *.
        do 2 zstep. zstep.
        ihere. to_implM.
        eapply KCALL; [exact ENV4 | exact LS4
          | intros errv PRE; apw W_set_bit.BN_set_bit_walk; [exact (bn_pre_le _ _ _ _ _ _ _ _ _ _ _ _ _ PRE STK_SETBIT) | reflexivity
                                                         | exact (W_mont.ref_at_montRR bs4 OWK PL0 am qm HPM0)
                                                         | exact (W_mont.wref_montRR PL0 am qm HPM0) | reflexivity | reflexivity | clear; lia]
          | hres |].
        intros u5 st5 bs5 m5 OW5 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV5 LS5 RS5 RES5. hnf in RES5. destruct RES5 as (_ & -> & _). unfold MallocRep.wz.
        assert (HAd5 : ref_at bs5 OW5 PL0 rd ad) by (apply (ref_at_stable _ _ _ _ PL0 _ _ RS5); apply ref_at_setbn; apply ref_at_set_mont; exact HAd).
        assert (HARi5 : ref_at bs5 OW5 PL0 rRi aRi) by (apply (ref_at_stable _ _ _ _ PL0 _ _ RS5); apply ref_at_setbn; apply ref_at_set_mont; exact HARi).
        clear ENV4 LS4.
        retpc 1050192.
        unfold implM. iprefix. zstep. if_false.
        ihere. to_implM.
        eapply L_A4; [exact RIR | exact ENV5 | exact LS5 | exact HAd5 | exact HARi5].
      Qed.

      Lemma L_A2 : forall j0 j1 js stK bsK mK OWK
          (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
        KENV (fr0 j0 j1 js) stK bsK mK OWK -> lib_state bsK mK OWK PL0 EA -> ref_at bsK OWK PL0 rd ad -> ref_at bsK OWK PL0 rRi aRi ->
        implM bgusegs (interp (embed (ms_a2 rd rRi bsK))) stK FINALQ
          (AMS rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (am + 24)) (Z_to_bv 64 aRi) t3 t4 t5 t6 0x1005c0 mK).
      Proof.
        intros until t6. intros ENVK LSK HAd HARi.
        pose proof SPR2 as SPR. pose proof ESPF as ESP. pose proof LO as LO'. pose proof GLO' as GLO2. unfold GLOBALS_TOP in GLO2.
        pose proof FBlo as FBL. pose proof LOF as LOFF.
        destruct (kenv_open LB PL0 EA lo B SPv FB s bs OW m CEIL FROK0 _ _ _ _ _ rd ad ENVK LSK HAd NROd)
          as (Dd & _ & _ & OKd & _ & _ & _ & _).
        pose proof OKd as (_ & _ & _ & OKd4).
        assert (CTd : Z.land (bn_flags (getbn rd bsK)) 4 = 0) by (destruct OKd4 as [E|E]; rewrite E; reflexivity).
        clear Dd OKd OKd4.
        unfold ms_a2. rewrite bbind_get_set0.
        unfold implM. iprefix. do 2 zstep. zstep.
        eapply KFLAGS; [exact ENVK | exact LSK | exact HAd | exact NROd | clear; lia |].
        intros m1 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV1 LS1. clear ENVK LSK.
        retpc 1050060. rewrite CTd.
        zstep. if_true.

        pose proof (W_mont.ref_at_montN bsK OWK PL0 am qm HPM0) as HAN.
        destruct (kenv_struct_store LB PL0 EA lo B SPv FB s bs OW m CEIL GLO' FBlo FBsp SPB B63 SPR2 FROK0 _ _ _ _ _ RMontN (am + 24) ENV1 LS1 HAN W_mont.RMontN_not_one)
          as (DN & BNN & OKN & _ & SEPN & _ & _ & CLOSEN).
        unfold BgRepDefs.bn_cells, MallocRep.wz in BNN.
        pose proof ENV1 as (_ & _ & ST1 & _ & MI1 & _).
        pose proof (munch_refl [(am + 24, am + 24 + 24)]%Z m1) as MU. pose proof (wmono_refl bgusegs m1) as WM.
        zstep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
        destruct (CLOSEN m2 (bn_with_neg (getbn RMontN bsK) false) MU WM) as (ENV2 & LS2);
          [ exact BNN | reflexivity | reflexivity | exact OKN | exact ST1 | exact MI1 |].
        clear BNN MU WM ST1 MI1 CLOSEN DN OKN SEPN ENV1 LS1.
        set (bs2 := setbn RMontN (bn_with_neg (getbn RMontN bsK) false) bsK) in *.

        pose proof ENV2 as (HEAP2 & _ & ST2 & (errv2 & ERR2) & MI2 & _ & _ & _ & _ & FR2 & _).
        pose proof (lib_state_h_parts _ _ _ _ _ _ LS2) as PARTS2.
        unfold LX_ERRNO, RATP in ERR2. change (3346328 - 164) with 3346164 in ERR2.
        unfold fr0, W_mont_set_b.saved in FR2. cbn [app] in FR2.
        change ([CB 8 j0; CB 8 j1; CB 24 js; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
          with ([CB 8 j0; CB 8 j1] ++ [CB 24 js] ++ [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) in FR2.
        apply bk_rw_cells_app in FR2. destruct FR2 as [FRa FR2]. change (Z.of_nat (cells_size [CB 8 j0; CB 8 j1])) with 16 in FR2.
        apply bk_rw_cells_app in FR2. destruct FR2 as [FRt FRs]. change (Z.of_nat (cells_size [CB 24 js])) with 24 in FRs.
        zstep. zstep.
        replace (Z_to_bv 64 (bv_unsigned sp + -80)) with (Z_to_bv 64 (FB + 16)) by (f_equal; clear; lia).
        eapply evt_cut.
        { eapply (bn_init_spec _ (Z_to_bv 64 FB)) with (lo := lo) (A := FB + 16) (junk := js);
            [exact FRt | rewrite ESP; exact ST2 | rewrite ESP; clear - LOFF CS128; lia | exact MI2 | rewrite ESP; right; clear; lia | reflexivity]. }
        intros ms' PO. unfold bn_small_post in PO.
        destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m3 & E & MUc & WMc & MIc & STc & (_ & RES)).
        subst ms'. rewrite ESP in *.
        retpc 1050088.
        eapply (rw_cells_transport bgusegs _ m2 m3) in FRa; [| exact MUc | exact WMc | cbn [disjoint_from cells_size csize Nat.add]; clear; lia].
        eapply (rw_cells_transport bgusegs _ m2 m3) in FRs; [| exact MUc | exact WMc | cbn [disjoint_from cells_size csize Nat.add]; clear; lia].
        eapply (rw_cells_transport bgusegs _ m2 m3) in ERR2; [| exact MUc | exact WMc | cbn [disjoint_from cells_size csize Nat.add]; clear - GLO2 FBL LOFF CS128; lia].
        assert (FR3 : rw_cells bgusegs m3 FB (fr1 j0 j1)).
        { unfold fr1. apply bk_rw_cells_app. split; [exact FRa|]. change (Z.of_nat (cells_size [CB 8 j0; CB 8 j1])) with 16.
          apply bk_rw_cells_app. split; [exact RES|]. change (Z.of_nat (cells_size (BgRepDefs.bn_cells 0 (bn_nil 0)))) with 24. exact FRs. }
        assert (ENV3 : KENV (fr1 j0 j1) stK bs2 m3 OWK).
        { assert (HWL : Forall (w_lib bs2 OWK PL0 lo SPv) [(FB - 16, FB); (FB + 16, FB + 16 + 24)]).
          { constructor; [left; cbn [fst snd]; clear - LOFF CS128; lia|]. constructor; [left; cbn [fst snd]; clear - FBL; lia| constructor]. }
          exact (kenv_silent LB PL0 EA lo B SPv FB s bs OW m CEIL GLO' FBlo FBsp SPB FROK0 _ _ stK bs2 m2 m3 OWK _ errv2
                   ENV2 PARTS2 MUc WMc HWL STc ERR2 MIc FR3 ltac:(cbn; clear; lia)). }
        assert (LS3 : lib_state bs2 m3 OWK PL0 EA).
        { eapply (lib_state_frame stK LB SPv B [] bs2 m2 m3 OWK PL0 EA _ HEAP2 LS2 MUc WMc FROK0).
          constructor; [apply w_stack; cbn [fst snd]; clear - LOFF CS128 CEIL; lia|]. constructor; [apply w_stack; cbn [fst snd]; clear - FBL CEIL; lia | constructor]. }
        clear FRa FRt FRs RES MUc WMc ST2 MI2 ERR2 HEAP2 PARTS2 ENV2 LS2 errv2.

        pose proof ENV3 as (HEAP3 & _ & ST3 & (errv3 & ERR3) & MI3 & _ & _ & _ & _ & _ & _).
        pose proof (lib_state_h_parts _ _ _ _ _ _ LS3) as PARTS3.
        pose proof (munch_refl [(FB, SPv)]%Z m3) as MU. pose proof (wmono_refl bgusegs m3) as WM.
        unfold LX_ERRNO, RATP in ERR3. change (3346328 - 164) with 3346164 in ERR3.
        unfold fr1, W_mont_set_b.saved, BgRepDefs.bn_cells, MallocRep.wz in FR3. cbn [app bn_nil bn_top bn_dmax bn_buf bn_neg bn_flags length Z.b2z Z.of_nat] in FR3.
        zstep. zstep. zstep. zstep. zstep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
        assert (ENV5 : KENV (fr2 j0 j1) stK bs2 m5 OWK).
        { eapply (kenv_silent LB PL0 EA lo B SPv FB s bs OW m CEIL GLO' FBlo FBsp SPB FROK0) with (W := [(FB, SPv)]) (errv' := errv3);
            [exact ENV3 | exact PARTS3 | exact MU | exact WM | constructor; [left; cbn [fst snd]; clear - FBL; lia | constructor]
            | exact ST3 | unfold LX_ERRNO, RATP; exact ERR3 | exact MI3 | exact FR3 | cbn; clear; lia]. }
        assert (LS5 : lib_state bs2 m5 OWK PL0 EA).
        { eapply (lib_state_frame stK LB SPv B [] bs2 m3 m5 OWK PL0 EA _ HEAP3 LS3 MU WM FROK0).
          constructor; [apply w_stack; cbn [fst snd]; clear - FBL CEIL; lia | constructor]. }
        clear FR3 MU WM ST3 MI3 ERR3 HEAP3 PARTS3 ENV3 LS3.
        ihere. to_implM.
        eapply L_A3; [exact ENV5 | exact LS5 | apply ref_at_setbn; exact HAd | apply ref_at_setbn; exact HARi].
      Qed.
    End Ri.

    Lemma L_A1 : forall j0 j1 js stK bsK mK OWK
        (rax t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 x19 x20 t3 t4 t5 t6 : word),
      KENV (fr0 j0 j1 js) stK bsK mK OWK -> lib_state bsK mK OWK PL0 EA -> ref_at bsK OWK PL0 rd ad ->
      implM bgusegs (interp (embed (ms_all rd bsK))) stK FINALQ
        (AMS rax t0 t1 t2 a0 (Z_to_bv 64 ad) a2 a3 a4 a5 a6 a7 x19 x20 t3 t4 t5 t6 0x100574 mK).
    Proof.
      intros until t6. intros ENVK LSK HAd.
      pose proof SPR2 as SPR. pose proof ESPF as ESP. pose proof LO as LO'. pose proof GLO' as GLO2. unfold GLOBALS_TOP in GLO2.
      pose proof FBlo as FBL. pose proof LOF as LOFF. pose proof AMR as (AM0 & AMC).
      unfold ms_all. rewrite bbind_get.
      unfold implM. iprefix. zstep. zstep.
      eapply KZERO; [exact ENVK | exact LSK | exact HAd | exact NROd |].
      intros m1 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV1 LS1. clear ENVK LSK.
      retpc 1049980.
      destruct (is_zero_pure (getbn rd bsK)) eqn:EZ; cbn [Z.b2z].
      { ihere. to_implM. unfold bunr. cbn [unreachable tree_ops embed interp]. apply implM_interp_unr. }
      zstep. if_true. zstep. zstep.
      ihere. to_implM.
      eapply KCALL; [exact ENV1 | exact LS1
        | intros errv PRE; apw W_ctx.BN_CTX_start_walk; [exact (bn_pre_le _ _ _ _ _ _ _ _ _ _ _ _ _ PRE STK_START) | reflexivity | exact HPC0 | reflexivity]
        | hres |].
      intros u2 st2 bs2 m2 OW2 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV2 LS2 RS2 _. clear ENV1 LS1.
      retpc 1050000.
      unfold implM. iprefix. zstep. zstep. ihere. to_implM.
      eapply KCALL; [exact ENV2 | exact LS2
        | intros errv PRE; apw W_ctx_get.BN_CTX_get_walk; [exact (bn_pre_le _ _ _ _ _ _ _ _ _ _ _ _ _ PRE STK_GET) | reflexivity | exact HPC0 | reflexivity]
        | hres |].
      intros rRi st3 bs3 m3 OW3 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV3 LS3 RS3 RES3. hnf in RES3. destruct RES3 as (_ & (iRi & ERi) & (aRi & HARi & ->) & _).
      pose proof (ref_at_stable _ _ _ _ PL0 _ _ RS3 (ref_at_stable _ _ _ _ PL0 _ _ RS2 HAd)) as HAd3.
      clear ENV2 LS2 RS2 RS3.
      retpc 1050008.
      assert (AiR : 0 < aRi < 2^64).
      { pose proof (ref_at_hrange _ _ _ _ _ _ _ _ _ (proj1 ENV3) (lib_state_h_parts _ _ _ _ _ _ LS3) HARi ltac:(rewrite ERi; apply hpl_pool)) as (R0 & RC & _).
        clear - R0 RC CEIL FBL SPR. lia. }
      unfold MallocRep.wz.
      unfold implM. iprefix.
      zstep. if_cases KR; rewrite ?unsigned_lit in KR by (clear - AiR; lia); zify_cond KR. { exfalso. clear - KR AiR. lia. }
      destruct (W_mont.ref_at_ualign_any _ _ _ _ _ _ _ _ _ (proj1 ENV3) (lib_state_h_parts _ _ _ _ _ _ LS3) (W_mont.ref_at_montRR bs3 OW3 PL0 am qm HPM0)) as (_ & AM8).
      ub. zstep.
      rewrite ms_mid_eq.
      ihere. to_implM.
      eapply KCALL; [exact ENV3 | exact LS3
        | intros errv PRE; apw W_copy.BN_copy_walk; [exact (bn_pre_le _ _ _ _ _ _ _ _ _ _ _ _ _ PRE STK_COPY) | reflexivity
                                                   | exact (W_mont.ref_at_montN bs3 OW3 PL0 am qm HPM0) | exact HAd3
                                                   | exact (hpl_wref PL0 RMontN (hpl_mont PL0 RMontN am qm eq_refl HPM0)) | exact NROd | reflexivity | reflexivity]
        | hres |].
      intros u4 st4 bs4 m4 OW4 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV4 LS4 RS4 RES4. hnf in RES4. destruct RES4 as (_ & -> & _). unfold MallocRep.wz.
      pose proof (ref_at_stable _ _ _ _ PL0 _ _ RS4 HAd3) as HAd4. pose proof (ref_at_stable _ _ _ _ PL0 _ _ RS4 HARi) as HARi4.
      clear ENV3 LS3 RS4.
      retpc 1050044.
      unfold implM. iprefix.
      zstep. if_cases KN; rewrite ?unsigned_lit in KN by (clear - AM0 AMC CEIL FBL SPR; lia); zify_cond KN. { exfalso. clear - KN AM0. lia. }
      ihere. to_implM.
      eapply (L_A2 rRi aRi (ex_intro _ iRi ERi)); [exact ENV4 | exact LS4 | exact HAd4 | exact HARi4].
    Qed.
  End Body.

  Lemma BN_MONT_CTX_set_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BgBnU.BnRep.err_addrs)
      (lo B : Z) (errv : word) (rd : bnref) (ad am ac : Z) (qm qc : bptr),
    bn_pre s bs m OW LB PL EA sp lo B errv (BN_MONT_CTX_SET_STACK CS) -> tp = wz RATP -> bv_unsigned sp mod 16 = 0 ->
    ref_at bs OW PL rd ad -> rd <> ROne -> pl_mont PL = Some (am, qm) -> pl_ctx PL = Some (ac, qc) -> pl_bn PL RTmod = None ->
    a0 = wz am -> a1 = wz ad -> a2 = wz ac ->
    implM bgusegs (interp (embed (BN_MONT_CTX_set (tree_ops bptr) rd bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_MONT_CTX_SET) fc None m (seg_rom bgusegs)).
  Proof.
    intros until qc. intros PRE -> SP16 HAd NROd HPM HPC HFT -> -> ->.
    pose proof PRE as (HEAP & LS & FROK & AUX & SPB & B63 & ST & CEIL & GLO & LO & ERR & MI).
    pose proof LO as LO'. unfold BN_MONT_CTX_SET_STACK in LO'.
    unfold BN_MONT_CTX_SET, MallocRep.wz.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
    pose proof PARTS as (_ & PWF & _ & (_ & _ & PM) & _). rewrite HPM in PM.
    pose proof (RH_range _ _ _ _ _ _ _ HEAP PM) as (M0 & _ & _ & MC1 & _). unfold MONT_CTX_SZ in MC1.
    assert (NTd : rd <> RTmod).
    { intros ->. apply ref_at_fixed in HAd; [|unfold RTmod, NFIX; clear; lia]. destruct HAd as (p & Ep & _).
      rewrite (pl_of_stored PL RTmod stored_tmod) in Ep. rewrite HFT in Ep. discriminate Ep. }
    pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgusegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3346328 - 164) with 3346164 in ERR.
    assert (GLO' : GLOBALS_TOP <= lo) by exact GLO. unfold GLOBALS_TOP in GLO.
    rewrite BN_MONT_CTX_set_eq.
    unfold implM. iprefix.
    carve_frame 96%nat ST. do 12 zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.

    apply (rw_cells_split_CB bgusegs _ _ [] 40 _ _ [8; 8; 24]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    lazymatch type of FR with rw_cells _ _ _ (CB 8 ?x0 :: CB 8 ?x1 :: CB 24 ?xs :: _) =>
      assert (FRJ : rw_cells bgusegs m1 (bv_unsigned sp + -96) (fr0 ra s0 s1 s2 s3 s4 s5 x0 x1 xs)) by exact FR
    end.
    clear FR.
    assert (HWL0 : Forall (w_lib bs OW PL lo (bv_unsigned sp)) [(bv_unsigned sp + -96, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
    assert (WOK0 : Forall (w_ok OW LB bs PL EA (bv_unsigned sp) []) [(bv_unsigned sp + -96, bv_unsigned sp)]) by (constructor; [apply w_stack; cbn; lia| constructor]).
    pose proof (lib_state_frame s LB _ _ [] bs m m1 OW PL EA _ HEAP LS MU WM FROK WOK0) as LS1.
    lazymatch type of FRJ with rw_cells _ _ _ ?fr =>
      assert (ENV : kenv LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -96) s bs OW m fr s bs m1 OW)
    end.
    { unfold kenv. split; [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL0 CEIL)|].
      split; [apply (seg_auxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK AUX MU WM HWL0 SPB ltac:(lia)); exact GLO'|].
      split; [exact ST|]. split; [exists errv; unfold LX_ERRNO, RATP; exact ERR|]. split; [exact MI|].
      split; [apply (seg_lx_pres _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL0 CEIL); [exact GLO'| lia]|].
      split; [reflexivity|]. split; [reflexivity|]. split; [apply refs_stable_refl|]. split; [exact FRJ| cbn; lia]. }
    assert (ADR : 0 < ad < 2^64).
    { pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK HAd NROd) as (A0 & AC & AI). lia. }
    ihere. to_implM.
    eapply (L_A1 ra gp sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo B s bs OW LB m PL EA rd ad am ac qm qc
              CEIL GLO' LO' SPB B63 FROK SP16 HPC HPM HFT PWF NROd NTd (conj M0 MC1) ADR);
      [exact ENV | exact LS1 | exact HAd].
  Qed.

End Proofs.
End WithCeiling0.
