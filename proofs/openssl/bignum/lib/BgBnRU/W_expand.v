(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnModel BnTree BnInv BnBridge BgState BgInv BgLib.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Import Layout Lib_iface Lib_kit F_memset F_memcpy.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnMem.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnTac.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnWU Require Import BnUTac.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnArr.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require Import BnHeap W_crypto BnUKit BnUKit2.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require BnRep.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgRepU Require Import BgRepDefs BgRep BgLayer BgIface BnUAlign.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Ltac to_implM :=
  lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
    lazymatch E with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition BN_EXPAND2 : Z := 0xfe108.
Definition BN_WEXPAND : Z := 0xfe3e0.
Definition BN_EXPAND2_STACK : Z := 48 + 8400.

Definition bn_expanded (b : bignum bptr) (pn : bptr) (words : nat) : bignum bptr :=
  mkBN (Some pn) (firstn (bn_top b) (bn_buf b) ++ repeat 0 (words - bn_top b)) (bn_top b) (bn_neg b) (bn_flags b).

Lemma bn_expanded_dmax : forall b pn words, (bn_top b <= bn_dmax b)%nat -> (bn_dmax b < words)%nat -> bn_dmax (bn_expanded b pn words) = words.
Proof. intros b pn words H1 H2. unfold bn_dmax, bn_expanded in *. cbn [bn_buf]. rewrite length_app, firstn_length_le, repeat_length by lia. lia. Qed.

Lemma expand_close : forall bs mF OWF PL EA r a pn An (words : nat),
  lib_state_h [r] bs mF OWF PL EA -> List.NoDup (map blk_id OWF) -> ref_at bs OWF PL r a -> r <> ROne ->
  rw_cells bgusegs mF a [C8 (wz An); C4 (wz (Z.of_nat (bn_top (getbn r bs)))); C4 (wz (Z.of_nat words));
                       C4 (wz (Z.b2z (bn_neg (getbn r bs)))); C4 (wz (bn_flags (getbn r bs)))] ->
  In (pn, An, Z.of_nat words * 8) OWF ->
  u64arr bgusegs mF An (wlimbs (firstn (bn_top (getbn r bs)) (bn_buf (getbn r bs)) ++ repeat 0 (words - bn_top (getbn r bs)))) ->
  ~ In pn (all_ids bs PL EA) -> (bn_dmax (getbn r bs) < words)%nat -> Z.of_nat words <= BG_DMAX ->
  lib_state (setbn r (bn_expanded (getbn r bs) pn words) bs) mF OWF PL EA
  /\ (words <= bn_dmax (getbn r (setbn r (bn_expanded (getbn r bs) pn words) bs)))%nat.
Proof.
  intros bs mF OWF PL EA r a pn An words LSH ND HA NRO BN HIN U FRESH HLT HMAX.
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LSH HA) as HV.
  pose proof (lib_state_h_parts _ _ _ _ _ _ LSH) as (WFS & PWF & IDS & PLB & ERRB).
  pose proof (st_wf_ok r bs WFS HV NRO) as (OK1 & OK2 & OK3 & OK4).
  set (b := getbn r bs) in *.
  pose proof (bn_expanded_dmax b pn words OK2 HLT) as EDM.
  split.
  - unfold lib_state. eapply (lib_state_close [] bs mF OWF PL EA r a); [exact LSH| exact ND| exact HA| exact NRO| | |].
    + exists An. split.
      * unfold bn_cells. rewrite EDM. exact BN.
      * unfold bn_arr. cbn [bn_expanded bn_d]. rewrite EDM. split; [rewrite Z.mul_comm; exact HIN| exact U].
    + unfold bg_ok. rewrite EDM. cbn [bn_expanded bn_buf bn_top bn_flags].
      split; [apply limbs_app; [apply limbs_firstn; exact OK1| apply limbs_repeat; exact limb_0]|]. split; [lia|]. split; [exact HMAX| exact OK4].
    + eapply ids_ok_setbn_new; [exact IDS| exact HV| reflexivity| exact FRESH].
  - rewrite getbn_setbn_same by exact HV. rewrite EDM. lia.
Qed.

Definition wexpand_res (r : bnref) (words : nat) (bs bs' : bstate bptr) : Prop :=
  ((words <= bn_dmax (getbn r bs))%nat /\ bs' = bs)
  \/ ((bn_dmax (getbn r bs) < words)%nat /\ exists pn, bs' = setbn r (bn_expanded (getbn r bs) pn words) bs).

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Lemma bn_expand2_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (r : bnref) (a : Z) (words : nat),
    bn_pre s bs m OW LB PL EA sp lo B errv BN_EXPAND2_STACK -> tp = wz RATP ->
    ref_at bs OW PL r a -> wref PL r -> a0 = wz a -> a1 = wz (Z.of_nat words) -> Z.of_nat words < 2^31 ->
    implM bgusegs (interp (embed (bn_wexpand (tree_ops bptr) r words bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA
               (fun _ bs' OW' PL' a0' => PL' = PL /\ a0' = wz a /\ (words <= bn_dmax (getbn r bs'))%nat /\ wexpand_res r words bs bs'
                                   /\ (forall q A n, In (q, A, n) OW -> bn_d (getbn r bs) <> Some q -> In (q, A, n) OW')))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_EXPAND2) fc None m (seg_rom bgusegs)).
  Proof.
    intros until words. intros (HEAP & LS & FROK & AUX & SPB & B63 & ST & CEIL & GLO & LO & ERR & MI) -> HA WR -> -> HW. pose proof (proj1 WR) as NRO.
    unfold BN_EXPAND2_STACK, BN_EXPAND2, GLOBALS_TOP, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
    destruct (lib_state_open [] bs m OW PL EA r a LS ND HA ltac:(intros []) NRO) as ((D & BN & ARR) & (OK1 & OK2 & OK3 & OK4) & LSH).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HA) as HV.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS. pose proof PARTS as (WFS & PWF & IDS & PLB & ERRB).
    pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK HA NRO) as (SA0 & SAC & SAI).
    destruct (bn_arr_facts s OW LB m HEAP bs PL EA _ _ PARTS FROK r D HV NRO ARR) as (U & LENW & D0 & DC & DI & DSEP).
    specialize (DSEP r a HA).
    set (b := getbn r bs) in *.
    unfold bn_cells in BN. unfold BG_DMAX in OK3.
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (a, a + 24)]%Z m) as MU. pose proof (wmono_refl bgusegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3346328 - 164) with 3346164 in ERR.
    unfold bn_wexpand, bbind, bget, bret, bunr, bmalloc, bfree_opt, bset, bfree.
    cbn [bind ret unreachable lib_malloc lib_free tree_ops tbind fst snd]. fold b.
    unfold implM. iprefix.
    destruct (ref_at_ualign s OW LB m bs PL EA r a HEAP PARTS HA NRO) as (PA0 & PA8).
    carve_frame 48%nat ST. do 8 step.
    chk ltac:(fun C => rewrite ?land64_small in C by (clear - PA0 SAC; lia); clear - C PA0 SAC; lia).
    step. step. rewrite (land7_wrap _ PA8).
    chk ltac:(fun C => clear - C; lia).
    step. step.
    unfold MallocRep.wz at 1. rewrite (sx32_small (Z.of_nat (bn_dmax b))) by lia.
    step. if_cases K; zify_cond K; rewrite !signed_small in K by lia.
    -
      replace (words <=? bn_dmax b)%nat with true by (symmetry; apply Nat.leb_le; lia).
      do 8 step. release_frame FR ST (bv_unsigned sp). step.
      ihere. to_implM. cbn [embed interp]. apply implM_ret. apply evt_done.
      lazymatch goal with |- bn_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mF end.
      assert (HWL : Forall (w_lib bs OW PL lo (bv_unsigned sp)) [(bv_unsigned sp + -48, bv_unsigned sp); (a, a + 24)]).
      { constructor; [left; cbn; lia|]. constructor; [|constructor]. right; right. exists r, a. split; [exact HA|]. split; [exact NRO|]. cbn. lia. }
      unfold bn_post. do 15 eexists. exists mF, OW, PL, errv. split; [reflexivity|]. cbn [fst snd].
      split; [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL)|].
      split. { unfold lib_state. rewrite <- (setbn_getbn_id r bs). fold b.
               eapply (lib_state_close [] bs mF OW PL EA r a b); [| exact ND| exact HA| exact NRO| | | ].
               - eapply (lib_state_frame s LB (bv_unsigned sp) B); [exact HEAP| exact LSH| exact MU| exact WM| exact FROK|].
                 constructor; [apply w_stack; cbn; lia|]. constructor; [|constructor].
                 eapply (w_struct OW LB bs PL EA (bv_unsigned sp) false [r] _ r a); [left; reflexivity| exact HA| exact NRO| cbn; lia| cbn; lia].
               - exists D. split; [unfold bn_cells; exact BN|]. eapply bn_arr_of_u64arr; [exact ARR| exact U].
               - unfold b. apply st_wf_ok; assumption.
               - apply ids_ok_setbn_same; [exact IDS| exact HV| reflexivity]. }
      split; [apply (seg_auxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK AUX MU WM HWL SPB ltac:(lia)); unfold GLOBALS_TOP; lia|]. split; [exact ST|].
      split; [unfold LX_ERRNO, RATP; exact ERR|]. split; [exact MI|].
      split; [apply (seg_lx_pres _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL); unfold GLOBALS_TOP; lia|].
      split; [reflexivity|]. split; [reflexivity|]. split; [apply refs_stable_refl|].
      split; [reflexivity|]. split; [reflexivity|]. split; [fold b; lia|]. split; [left; split; [fold b; lia| reflexivity]|]. intros q0 A0 n0 Hq0 _. exact Hq0.
    -
      replace (words <=? bn_dmax b)%nat with false by (symmetry; apply Nat.leb_gt; lia).
      step. step. if_cases K2; zify_cond K2; rewrite ?signed_small in K2 by lia.
      {
        replace (BN_WORDS_MAX <? Z.of_nat words) with true by (symmetry; apply Z.ltb_lt; unfold BN_WORDS_MAX; lia).
        ihere. to_implM. cbn [embed interp]. apply implM_interp_unr. }
      replace (BN_WORDS_MAX <? Z.of_nat words) with false by (symmetry; apply Z.ltb_ge; unfold BN_WORDS_MAX; lia).
      destruct (Z.ltb_spec 512 (Z.of_nat words)) as [K512|K512].
      {
        ihere. to_implM. cbn [embed interp]. apply implM_interp_unr. }
      assert (FLR : 0 <= bn_flags b <= 1) by (destruct OK4 as [E|E]; rewrite E; lia).
      assert (EL2 : Z.land (bn_flags b) 2 = 0) by (destruct OK4 as [E|E]; rewrite E; reflexivity).
      assert (EL8 : Z.land (bn_flags b) 8 = 0) by (destruct OK4 as [E|E]; rewrite E; reflexivity).
      unfold has_flag, BN_FLG_STATIC_DATA, BN_FLG_SECURE. rewrite EL2, EL8. cbn [Z.eqb negb].
      step. unfold MallocRep.wz at 1. rewrite (zx32_small (bn_flags b)) by lia.
      step. rewrite (unsigned_lit (bn_flags b)), EL2 by lia. step. if_false.
      step. rewrite (unsigned_lit (bn_flags b)), EL8 by lia. step. if_false.
      do 6 step.

      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
      assert (HWL : Forall (w_lib bs OW PL lo (bv_unsigned sp)) [(bv_unsigned sp + -48, bv_unsigned sp); (a, a + 24)]).
      { constructor; [left; cbn; lia|]. constructor; [|constructor]. right; right. exists r, a. split; [exact HA|]. split; [exact NRO|]. cbn. lia. }
      assert (HEAP1 : RHEAP s (OW ++ LB) m1) by (exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL)).
      assert (AUX1 : rauxv_ok m1 B) by (apply (seg_auxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK AUX MU WM HWL SPB ltac:(lia)); unfold GLOBALS_TOP; lia).
      assert (LSH1 : lib_state_h [r] bs m1 OW PL EA).
      { eapply (lib_state_frame s LB (bv_unsigned sp) B); [exact HEAP| exact LSH| exact MU| exact WM| exact FROK|].
        constructor; [apply w_stack; cbn; lia|]. constructor; [|constructor].
        eapply (w_struct OW LB bs PL EA (bv_unsigned sp) false [r] _ r a); [left; reflexivity| exact HA| exact NRO| cbn; lia| cbn; lia]. }
      assert (LXP1 : lx_pres LB (bv_unsigned sp) (XW PL) m m1) by (apply (seg_lx_pres _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL); unfold GLOBALS_TOP; lia).
      assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
      ihere. to_implM. cbn [embed]. replace (8 * Z.of_nat words) with (Z.of_nat words * 8) by lia.
      eapply (CRYPTO_calloc_walk HM) with (B := B) (lo := lo) (errv := errv) (num := Z.of_nat words) (size := 8);
        [exact HEAP1 | exact AUX1 | rewrite ESP; lia | rewrite ESP; exact ST | exact CEIL | unfold GLOBALS_TOP; lia
        | rewrite ESP; unfold CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RMALLOC_STACK; lia
        | unfold LX_ERRNO, RATP; exact ERR | exact MI | reflexivity
        | exact (proj1 LSH1) | reflexivity | reflexivity | lia | lia | lia | reflexivity | ].
      intros pn st1 ms1 PO. unfold calloc_post in PO. rewrite ?ESP in PO.
      destruct PO as (r5 & r6 & r7 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m3 & An & errv2
                      & -> & MI3 & ST3 & ERR3 & AUX3 & HP & FA & SO & BR & HEAP3 & BLK).
      replace (ret_pc (Z_to_bv 64 1040760)) with (Z_to_bv 64 1040760) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

      pose proof (agree_of_heap_pres _ _ _ _ HP) as AGP.
      apply (rw_cells_agree _ _ _ _ _ AGP) in FR; [| intros x Hx; left; cbn in Hx; lia].
      apply (rw_cells_agree _ _ _ _ _ AGP) in BN; [| intros x Hx; cbn in Hx; eapply (ref_at_client _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK HA NRO); [lia| intros b0 Hb0; apply in_or_app; left; exact Hb0| lia]].
      assert (LSH3 : lib_state_h [r] bs m3 OW PL EA).
      { eapply (lib_state_h_heap_pres _ _ _ _ _ _ _ _ _ (bv_unsigned sp) B); [exact LSH1| exact FROK| | exact HP|]; [lia|]. intros b0 Hb0. apply in_or_app. left. exact Hb0. }
      assert (ARR3 : bn_arr m3 OW (pl_of PL r) D b).
      { eapply bn_arr_of_u64arr; [exact ARR|]. eapply BnRep.u64arr_agree; [exact AGP| exact U|]. intros x Hx. rewrite wlimbs_length in Hx.
        eapply (bn_arr_rclient bs OW PL EA (bv_unsigned sp) B); [exact HEAP| exact PARTS| exact FROK| exact HV| exact NRO| exact ARR| lia| | subst b; unfold bn_dmax; lia].
        intros b0 Hb0. apply in_or_app. left. exact Hb0. }
      clear U.
      pose proof BR as (BA0 & BA16 & _ & BAC & BAI).
      assert (ND3 : List.NoDup (map blk_id ((pn, An, Z.of_nat words * 8) :: OW ++ LB))) by (eapply LH_nodup; exact HEAP3).
      assert (FRESH : ~ In pn (map blk_id (OW ++ LB))) by (cbn [map] in ND3; apply NoDup_cons_iff in ND3; exact (proj1 ND3)).
      assert (NEWSEP : forall q A n, In (q, A, n) OW -> An + Z.of_nat words * 8 <= A \/ A + n <= An).
      { intros q A n Hq. assert (NE : pn <> q) by (intros ->; apply FRESH; rewrite map_app; apply in_or_app; left; apply (in_map blk_id) in Hq; exact Hq).
        exact (LH_disjoint _ _ _ (pn, An, Z.of_nat words * 8) (q, A, n) HEAP3 ltac:(left; reflexivity) ltac:(right; apply in_or_app; left; exact Hq) NE). }
      pose proof (ref_at_fresh_sep bs OW PL EA (bv_unsigned sp) B _ _ _ r a pn An _ HEAP3 PARTS FROK HA NRO) as SEPs.
      set (OW1 := (pn, An, Z.of_nat words * 8) :: OW).
      assert (LSH3' : lib_state_h [r] bs m3 OW1 PL EA) by (eapply lib_state_h_ow; [exact LSH3|]; intros q A n _ Hq; right; exact Hq).
      pose proof (lib_state_h_parts _ _ _ _ _ _ LSH3') as PARTS1.
      assert (HA1 : ref_at bs OW1 PL r a) by (eapply ref_at_ow_mono; [| exact HA]; intros b0 Hb0; right; exact Hb0).
      cbn [tbind fst snd].
      unfold LX_ERRNO, RATP in ERR3. change (3346328 - 164) with 3346164 in ERR3.
      assert (FRESHA : ~ In pn (all_ids bs PL EA)).
      { intros Hin. apply FRESH. rewrite map_app. apply in_or_app. left. eapply all_ids_owned; eauto. }
      assert (LXP3 : lx_pres LB (bv_unsigned sp) (XW PL) m m3).
      { eapply lx_pres_trans; [exact LXP1|]. apply lx_pres_of_heap_pres.
        eapply rheap_pres_weaken; [exact HP| lia|]. intros b0 Hb0. apply in_or_app. right. exact Hb0. }
      assert (HinN : In (pn, An, Z.of_nat words * 8) OW1) by (left; reflexivity).
      assert (ND1 : List.NoDup (map blk_id OW1)) by (eapply (RH_nodup_l st1 OW1 LB m3); exact HEAP3).
      destruct (bn_d b) as [pd|] eqn:Ed.
      2:{
        destruct (bn_arr_null PL r m3 OW D b PWF WR Ed ARR3) as [-> Eb]. assert (ED0 : bn_dmax b = 0%nat) by (unfold bn_dmax; rewrite Eb; reflexivity).
        assert (ET0 : bn_top b = 0%nat) by lia.
        pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp); (a, a + 24)]%Z m3) as MU3. pose proof (wmono_refl bgusegs m3) as WM3.
        unfold bret. cbn [ret tree_ops tbind embed interp fst snd]. apply implM_ret.
        unfold MallocRep.wz in *.
        do 3 step. if_cases KA; zify_cond KA; [exfalso; rewrite ?unsigned_lit in KA by lia; lia|]. clear KA.
        step. replace (sx32 (Z_to_bv 64 (Z.of_nat (bn_top b)))) with (Z_to_bv 64 0) by (rewrite ET0; reflexivity).
        step. step. if_true. step. if_true.
        step. step. do 8 step. release_frame FR ST3 (bv_unsigned sp). step.
        apply evt_done.
        lazymatch goal with |- bn_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mF end.
        assert (HWL3 : Forall (w_lib bs OW1 PL lo (bv_unsigned sp)) [(bv_unsigned sp + -48, bv_unsigned sp); (a, a + 24)]).
        { constructor; [left; cbn; lia|]. constructor; [|constructor]. right; right. exists r, a. split; [exact HA1|]. split; [exact NRO|]. cbn. lia. }
        assert (LSHF : lib_state_h [r] bs mF OW1 PL EA).
        { eapply (lib_state_frame st1 LB (bv_unsigned sp) B); [exact HEAP3| exact LSH3'| exact MU3| exact WM3| exact FROK|].
          constructor; [apply w_stack; cbn; lia|]. constructor; [|constructor].
          eapply (w_struct OW1 LB bs PL EA (bv_unsigned sp) false [r] _ r a); [left; reflexivity| exact HA1| exact NRO| cbn; lia| cbn; lia]. }
        assert (UF : u64arr bgusegs mF An (wlimbs (firstn (bn_top b) (bn_buf b) ++ repeat 0 (words - bn_top b)))).
        { rewrite ET0, Eb. cbn [firstn app]. rewrite Nat.sub_0_r. apply (CB_u64arr bgusegs mF An (Z.to_nat (Z.of_nat words * 8))).
          unfold wlimbs. rewrite map_repeat, u64s_repeat0. replace (8 * words)%nat with (Z.to_nat (Z.of_nat words * 8)) by lia. exact BLK. }
        destruct (expand_close bs mF OW1 PL EA r a pn An words LSHF ND1 HA1 NRO) as [LSF RESF];
          [fold b; exact BN| exact HinN| fold b; exact UF| exact FRESHA| fold b; lia| unfold BG_DMAX; lia|].
        unfold bn_post. do 15 eexists. exists mF, OW1, PL, errv2. split; [reflexivity|]. cbn [fst snd].
        fold (bn_expanded b pn words). fold b in LSF, RESF.
        split; [exact (seg_heap st1 bs OW1 LB PL EA _ _ m3 mF _ lo _ HEAP3 PARTS1 FROK MU3 WM3 HWL3 CEIL)|]. split; [exact LSF|].
        split; [apply (seg_auxv st1 bs OW1 LB PL EA _ _ m3 mF _ lo _ B HEAP3 PARTS1 FROK AUX3 MU3 WM3 HWL3 SPB ltac:(lia)); unfold GLOBALS_TOP; lia|]. split; [exact ST3|].
        split; [unfold LX_ERRNO, RATP; exact ERR3|]. split; [exact MI3|].
        split. { eapply lx_pres_trans; [exact LXP3|]. apply (seg_lx_pres st1 bs OW1 LB PL EA _ _ m3 mF _ lo _ HEAP3 PARTS1 FROK MU3 WM3 HWL3 CEIL); unfold GLOBALS_TOP; lia. }
        split; [exact FA|]. split; [exact SO|].
        split. { apply refs_stable_ow; [reflexivity|]. intros q H _ Hq. right. exact Hq. }
        split; [reflexivity|]. split; [reflexivity|]. split; [exact RESF|]. split; [right; split; [fold b; lia|]; exists pn; reflexivity|].
        intros q0 A0 n0 Hq0 _. right. exact Hq0. }

      unfold bn_arr in ARR3. rewrite Ed in ARR3. destruct ARR3 as [HinD U3].
      pose proof (RH_range _ _ _ _ _ _ _ HEAP HinD) as (DA0 & DA16 & _ & _ & _).
      pose proof (NEWSEP _ _ _ HinD) as SEPd.
      set (newbuf := firstn (bn_top b) (bn_buf b) ++ repeat 0 (words - bn_top b)).
      cbn [tbind embed fst snd].

      eapply implM_evt with (P := fun ms' => exists ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m4,
          ms' = MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 RATP) t0' t1' t2' sp (Z_to_bv 64 a)
                        a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (Z.of_nat words)) (Z_to_bv 64 An) (Z_to_bv 64 D)
                        s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                   F (Z_to_bv 64 1040840) fc None m4 (seg_rom bgusegs)
          /\ munch [(An, An + Z.of_nat words * 8)] m3 m4 /\ wmono bgusegs m3 m4 /\ mem_inv bgusegs m4
          /\ stk bgusegs m4 lo (bv_unsigned sp + -48)
          /\ rw_cells bgusegs m4 (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
          /\ rw_cells bgusegs m4 a [C8 (wz D); C4 (wz (Z.of_nat (bn_top b))); C4 (wz (Z.of_nat (bn_dmax b))); C4 (wz (Z.b2z (bn_neg b))); C4 (wz (bn_flags b))]
          /\ rw_cells bgusegs m4 3346164 [C4 errv2]
          /\ u64arr bgusegs m4 D (wlimbs (bn_buf b)) /\ u64arr bgusegs m4 An (wlimbs newbuf)).
      { pose proof (munch_refl [(An, An + Z.of_nat words * 8)]%Z m3) as MU3. pose proof (wmono_refl bgusegs m3) as WM3.
        unfold MallocRep.wz in *.
        do 3 step. if_cases KA; zify_cond KA; [exfalso; rewrite ?unsigned_lit in KA by lia; lia|]. clear KA.
        step. rewrite (sx32_small (Z.of_nat (bn_top b))) by lia. step. step.
        if_cases KT; zify_cond KT.
        -
          assert (ET0 : bn_top b = 0%nat).
          { apply andb_false_iff in KT. destruct KT as [KT|KT]; apply Z.ltb_ge in KT; lia. }
          apply evt_done. do 16 eexists. exists m3. split; [reflexivity|].
          split; [exact MU3|]. split; [exact WM3|]. split; [exact MI3|]. split; [exact ST3|]. split; [exact FR|]. split; [exact BN|].
          split; [exact ERR3|]. split; [exact U3|].
          subst newbuf. rewrite ET0. cbn [firstn app]. rewrite Nat.sub_0_r. apply (CB_u64arr bgusegs m3 An (Z.to_nat (Z.of_nat words * 8))).
          rewrite lbytes_repeat0. replace (8 * words)%nat with (Z.to_nat (Z.of_nat words * 8)) by lia. exact BLK.
        -
          assert (TOPP : (0 < bn_top b)%nat) by lia.
          step. step.
          rewrite (lor_land7 An D) by (clear - BA16 DA16; Z.div_mod_to_equations; lia).
          chk ltac:(fun C => clear - C; lia).
          do 5 step.
          rewrite ?(unsigned_lit (Z.of_nat (bn_top b))) by lia.
          replace (Z.shiftl (Z.of_nat (bn_top b)) 3) with (Z.of_nat (bn_top b) * 8) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity).

          assert (SRC : bytes_at bgusegs m3 D (u64s (wlimbs (firstn (bn_top b) (bn_buf b))))).
          { apply limbarr_bytes. apply (proj1 (limbarr_split bgusegs m3 D (bn_buf b) (bn_top b) ltac:(unfold bn_dmax in *; lia))) in U3. exact (proj1 U3). }
          assert (ZSPLIT : u8arr bgusegs m3 An (repeat (Z_to_bv 8 0) (8 * bn_top b) ++ repeat (Z_to_bv 8 0) (8 * (words - bn_top b)))).
          { rewrite <- repeat_app. replace (8 * bn_top b + 8 * (words - bn_top b))%nat with (Z.to_nat (Z.of_nat words * 8)) by lia.
            eapply u8arr_of_rw_cells. exact BLK. }
          apply u8arr_app in ZSPLIT. destruct ZSPLIT as [Z1 Z2]. rewrite repeat_length in Z2.
          apply rw_cells_of_u8arr in Z1. rewrite repeat_length in Z1.
          eapply evt_cut.
          { eapply (memcpy_callZ (Z_to_bv 64 1040840) (Z_to_bv 64 (bv_unsigned sp + -48))) with (Dst := An) (Src := D) (N := Z.of_nat (bn_top b) * 8)
              (src := u64s (wlimbs (firstn (bn_top b) (bn_buf b)))) (junk := repeat (Z_to_bv 8 0) (8 * bn_top b));
              [exact SRC| rewrite u64s_length, wlimbs_len, firstn_length_le by (unfold bn_dmax in *; lia); lia
              | replace (Z.to_nat (Z.of_nat (bn_top b) * 8)) with (8 * bn_top b)%nat by lia; exact Z1
              | lia | lia | lia | lia | exact MI3]. }
          clear BLK. post_call bgusegs m3.
          apply evt_done. do 16 eexists. exists x13. split; [reflexivity|].
          split; [exact MU3|]. split; [exact WM3|]. split; [exact MI0|]. split; [exact ST3|]. split; [exact FR|]. split; [exact BN|].
          split; [exact ERR3|]. split; [exact U3|].
          subst newbuf. apply u64arr_u8arr. rewrite wlimbs_app, u64s_app. apply u8arr_app. split.
          + eapply u8arr_of_rw_cells. exact PC.
          + rewrite u64s_length, wlimbs_len, firstn_length_le by (unfold bn_dmax in *; lia). rewrite lbytes_repeat0. exact Z2. }
      cbv beta. intros ms4 (ra' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m4
                            & -> & MU4 & WM4 & MI4 & ST4 & FR4 & BN4 & ERR4 & U4 & UN4).
      clear BLK U3 FR BN ERR3 ST3 MI3.

      pose proof (munch_refl [(bv_unsigned sp + -64, bv_unsigned sp + -48)]%Z m4) as MU5. pose proof (wmono_refl bgusegs m4) as WM5.
      assert (HWL4 : Forall (w_lib bs OW1 PL lo (bv_unsigned sp)) [(An, An + Z.of_nat words * 8)]).
      { constructor; [|constructor]. right; left. exists (pn, An, Z.of_nat words * 8). cbn. split; [exact HinN| lia]. }
      assert (HEAP4 : RHEAP st1 (OW1 ++ LB) m4) by (exact (seg_heap st1 bs OW1 LB PL EA _ _ m3 m4 _ lo _ HEAP3 PARTS1 FROK MU4 WM4 HWL4 CEIL)).
      assert (AUX4 : rauxv_ok m4 B) by (apply (seg_auxv st1 bs OW1 LB PL EA _ _ m3 m4 _ lo _ B HEAP3 PARTS1 FROK AUX3 MU4 WM4 HWL4 SPB ltac:(lia)); unfold GLOBALS_TOP; lia).
      assert (LXP4 : lx_pres LB (bv_unsigned sp) (XW PL) m m4).
      { eapply lx_pres_trans; [exact LXP3|]. apply (seg_lx_pres st1 bs OW1 LB PL EA _ _ m3 m4 _ lo _ HEAP3 PARTS1 FROK MU4 WM4 HWL4 CEIL); unfold GLOBALS_TOP; lia. }
      assert (LSH4 : lib_state_h [r] bs m4 OW1 PL EA).
      { eapply (lib_state_frame st1 LB (bv_unsigned sp) B); [exact HEAP3| exact LSH3'| exact MU4| exact WM4| exact FROK|]. constructor; [|constructor].
        eapply (w_foreign OW1 LB bs PL EA (bv_unsigned sp) false [r] _ pn An (Z.of_nat words * 8)); [left; reflexivity| exact FRESHA| cbn; lia| cbn; lia]. }
      clear LSH3' LSH3 LSH1 LSH HEAP3 AUX3 HEAP1 AUX1 MU4 WM4.
      assert (LENN : Z.of_nat (length (wlimbs newbuf)) = Z.of_nat words).
      { subst newbuf. rewrite wlimbs_len, length_app, firstn_length_le, repeat_length by (unfold bn_dmax in *; lia). lia. }
      unfold MallocRep.wz in BN4. apply (flag_cell_split bgusegs m4 a _ _ _ _ (bn_flags b) FLR) in BN4.
      unfold MallocRep.wz in *.
      unfold implM. iprefix.
      step. if_cases KD; zify_cond KD; [exfalso; rewrite ?unsigned_lit in KD by lia; lia|]. clear KD.
      do 3 step.
      remember (Z_to_bv 64 1040856) as ra1 eqn:Era1.
      carve_frame 16%nat ST4. do 4 step.
      step. rewrite (land7_wrap _ PA8).
      chk ltac:(fun C => clear - C; lia).
      step.
      rewrite (zxb_small (bn_flags b)) by lia.
      step. rewrite (unsigned_lit (bn_flags b)), EL8 by lia. step. if_false.
      step. if_false.
      step. rewrite (sx32_small (Z.of_nat (bn_dmax b))) by lia.
      step.
      do 4 step. rewrite ?(unsigned_lit (Z.of_nat (bn_dmax b))) by lia.
      replace (Z.shiftl (Z.of_nat (bn_dmax b)) 3) with (Z.of_nat (bn_dmax b) * 8) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
      do 3 step. release_frame FR ST4 (bv_unsigned sp + -48). subst ra1. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
      assert (HWL5 : Forall (w_lib bs OW1 PL lo (bv_unsigned sp)) [(bv_unsigned sp + -64, bv_unsigned sp + -48)]).
      { constructor; [|constructor]. left. cbn. lia. }
      assert (HEAP5 : RHEAP st1 (OW1 ++ LB) m5) by (exact (seg_heap st1 bs OW1 LB PL EA _ _ m4 m5 _ lo _ HEAP4 PARTS1 FROK MU5 WM5 HWL5 CEIL)).
      assert (AUX5 : rauxv_ok m5 B) by (apply (seg_auxv st1 bs OW1 LB PL EA _ _ m4 m5 _ lo _ B HEAP4 PARTS1 FROK AUX4 MU5 WM5 HWL5 SPB ltac:(lia)); unfold GLOBALS_TOP; lia).
      assert (LXP5 : lx_pres LB (bv_unsigned sp) (XW PL) m m5).
      { eapply lx_pres_trans; [exact LXP4|]. apply (seg_lx_pres st1 bs OW1 LB PL EA _ _ m4 m5 _ lo _ HEAP4 PARTS1 FROK MU5 WM5 HWL5 CEIL); unfold GLOBALS_TOP; lia. }
      assert (LSH5 : lib_state_h [r] bs m5 OW1 PL EA).
      { eapply (lib_state_frame st1 LB (bv_unsigned sp) B); [exact HEAP4| exact LSH4| exact MU5| exact WM5| exact FROK|]. constructor; [|constructor]. apply w_stack; cbn; lia. }
      assert (HinD1 : In (pd, D, 8 * Z.of_nat (bn_dmax b)) OW1) by (right; exact HinD).
      pose proof (limbarr_CB bgusegs m5 D (bn_buf b) U4) as OLD.
      ihere. to_implM.
      eapply (CRYPTO_clear_free_walk HF) with (B := B) (lo := lo) (errv := errv2) (p := pd) (A := D) (n := 8 * Z.of_nat (bn_dmax b))
          (num := Z.of_nat (bn_dmax b) * 8) (junk := u64s (wlimbs (bn_buf b)));
        [exact HEAP5 | apply in_or_app; left; exact HinD1 | exact AUX5 | rewrite ESP; lia | rewrite ESP; exact ST4 | exact CEIL | unfold GLOBALS_TOP; lia
        | rewrite ESP; unfold CRYPTO_CLEAR_FREE_STACK, RFREE_STACK; lia | unfold LX_ERRNO, RATP; exact ERR4 | exact MI4 | reflexivity
        | exact (proj1 LSH5) | replace (Z.to_nat (Z.of_nat (bn_dmax b) * 8)) with (8 * length (bn_buf b))%nat by (unfold bn_dmax; lia); exact OLD
        | lia | reflexivity | reflexivity | ].
      intros st6 ms6 PO. unfold cfree_post in PO. rewrite ?ESP in PO.
      destruct PO as (q5 & q6 & q7 & q10 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & m6
                      & -> & MI6 & ST6 & ERR6 & AUX6 & HP6 & FA6 & SO6 & HEAP6).
      replace (ret_pc (Z_to_bv 64 1040856)) with (Z_to_bv 64 1040856) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      assert (NDL : List.NoDup (map blk_id (OW1 ++ LB))) by (eapply LH_nodup; exact HEAP5).
      assert (EL : lb_remove pd (OW1 ++ LB) = lb_remove pd OW1 ++ LB).
      { apply lb_remove_app_l; [exact NDL|]. apply (in_map blk_id) in HinD1. exact HinD1. }
      rewrite EL in HP6, HEAP6. set (OWF := lb_remove pd OW1) in *.
      assert (NEpn : pn <> pd).
      { intros ->. apply FRESH. rewrite map_app. apply in_or_app. left. apply (in_map blk_id) in HinD. exact HinD. }
      assert (HinNF : In (pn, An, Z.of_nat words * 8) OWF) by (apply lb_remove_In; split; [exact HinN| exact NEpn]).
      assert (NDF : List.NoDup (map blk_id OWF)) by (eapply (RH_nodup_l st6 OWF LB m6); exact HEAP6).
      assert (LSH6 : lib_state_h [r] bs m6 OWF PL EA).
      { eapply (lib_state_h_free st1 LB [r] bs m5 m6 OW1 PL EA r pd D _ (bv_unsigned sp) B); [exact HEAP5| exact LSH5| exact FROK| | left; reflexivity| exact HV| exact Ed| exact HinD1| rewrite EL; exact HP6].
        lia. }
      assert (HAF : ref_at bs OWF PL r a) by (eapply (ref_at_lb_remove bs OW1 PL EA r pd); [exact PARTS1| exact HV| exact Ed| exact HA1]).
      pose proof (lib_state_h_parts _ _ _ _ _ _ LSH6) as PARTSF.
      assert (HEAP6' : RHEAP st6 (OWF ++ LB) m6) by exact HEAP6.
      pose proof (agree_of_heap_pres _ _ _ _ HP6) as AGP6.
      apply (rw_cells_agree _ _ _ _ _ AGP6) in FR4; [| intros x Hx; left; cbn in Hx; lia].
      apply (rw_cells_agree _ _ _ _ _ AGP6) in BN4; [| intros x Hx; cbn in Hx; eapply (ref_at_client _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP6' PARTSF FROK HAF NRO); [lia| intros b0 Hb0; apply in_or_app; left; exact Hb0| lia]].
      apply (BnRep.u64arr_agree _ _ _ _ _ AGP6) in UN4; [| intros x Hx; right; right; exists (pn, An, Z.of_nat words * 8); split; [apply in_or_app; left; exact HinNF| cbn [blk_addr blk_size fst snd]; lia]].
      apply (flag_cell_join bgusegs m6 a _ _ _ _ (bn_flags b) FLR) in BN4.
      cbn [embed interp]. apply implM_ret.
      pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp); (a, a + 24)]%Z m6) as MU7. pose proof (wmono_refl bgusegs m6) as WM7.
      unfold LX_ERRNO, RATP in ERR6. change (3346328 - 164) with 3346164 in ERR6.
      clear U4 OLD MU5 WM5.
      step. step. do 8 step. release_frame FR4 ST6 (bv_unsigned sp). step.
      apply evt_done.
      lazymatch goal with |- bn_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mF end.
      assert (HWL7 : Forall (w_lib bs OWF PL lo (bv_unsigned sp)) [(bv_unsigned sp + -48, bv_unsigned sp); (a, a + 24)]).
      { constructor; [left; cbn; lia|]. constructor; [|constructor]. right; right. exists r, a. split; [exact HAF|]. split; [exact NRO|]. cbn. lia. }
      assert (LSHF : lib_state_h [r] bs mF OWF PL EA).
      { eapply (lib_state_frame st6 LB (bv_unsigned sp) B); [exact HEAP6| exact LSH6| exact MU7| exact WM7| exact FROK|].
        constructor; [apply w_stack; cbn; lia|]. constructor; [|constructor].
        eapply (w_struct OWF LB bs PL EA (bv_unsigned sp) false [r] _ r a); [left; reflexivity| exact HAF| exact NRO| cbn; lia| cbn; lia]. }
      destruct (expand_close bs mF OWF PL EA r a pn An words LSHF NDF HAF NRO) as [LSF RESF];
        [fold b; exact BN4| exact HinNF| fold b; exact UN4| exact FRESHA| fold b; lia| unfold BG_DMAX; lia|].
      unfold bn_post. do 15 eexists. exists mF, OWF, PL, errv2. split; [reflexivity|]. cbn [fst snd].
      fold (bn_expanded b pn words). fold b in LSF, RESF.
      split; [exact (seg_heap st6 bs OWF LB PL EA _ _ m6 mF _ lo _ HEAP6 PARTSF FROK MU7 WM7 HWL7 CEIL)|]. split; [exact LSF|].
      split; [apply (seg_auxv st6 bs OWF LB PL EA _ _ m6 mF _ lo _ B HEAP6 PARTSF FROK AUX6 MU7 WM7 HWL7 SPB ltac:(lia)); unfold GLOBALS_TOP; lia|]. split; [exact ST6|].
      split; [unfold LX_ERRNO, RATP; exact ERR6|]. split; [exact MI6|].
      split. { eapply lx_pres_trans; [exact LXP5|]. eapply lx_pres_trans.
               - apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HP6| lia|]. intros b0 Hb0. apply in_or_app. right. exact Hb0.
               - apply (seg_lx_pres st6 bs OWF LB PL EA _ _ m6 mF _ lo _ HEAP6 PARTSF FROK MU7 WM7 HWL7 CEIL); unfold GLOBALS_TOP; lia. }
      split; [congruence|]. split; [congruence|].
      split. { apply refs_stable_ow; [reflexivity|]. intros q H Hq HinH. apply lb_remove_In. split; [right; exact HinH|]. cbn [blk_id fst]. intros ->.
               eapply (ids_bn_item_neq r bs pd pd); eauto using ids_m_nodup. }
      split; [reflexivity|]. split; [reflexivity|]. split; [exact RESF|]. split; [right; split; [fold b; lia|]; exists pn; reflexivity|].
      intros q0 A0 n0 Hq0 NE0. apply lb_remove_In. split; [right; exact Hq0|]. cbn [blk_id fst]. intros ->. apply NE0. reflexivity.
  Qed.

  Definition BN_WEXPAND_STACK : Z := 16 + BN_EXPAND2_STACK.

  Lemma bn_wexpand_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (r : bnref) (a : Z) (words : nat),
    bn_pre s bs m OW LB PL EA sp lo B errv BN_WEXPAND_STACK -> tp = wz RATP ->
    ref_at bs OW PL r a -> wref PL r -> a0 = wz a -> a1 = wz (Z.of_nat words) -> Z.of_nat words < 2^31 ->
    implM bgusegs (interp (embed (bn_wexpand (tree_ops bptr) r words bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA
               (fun _ bs' OW' PL' a0' => PL' = PL /\ a0' = wz a /\ (words <= bn_dmax (getbn r bs'))%nat /\ wexpand_res r words bs bs'
                                   /\ (forall q A n, In (q, A, n) OW -> bn_d (getbn r bs) <> Some q -> In (q, A, n) OW')))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_WEXPAND) fc None m (seg_rom bgusegs)).
  Proof.
    intros until words. intros (HEAP & LS & FROK & AUX & SPB & B63 & ST & CEIL & GLO & LO & ERR & MI) -> HA WR -> -> HW. pose proof (proj1 WR) as NRO.
    unfold BN_WEXPAND_STACK, BN_EXPAND2_STACK, BN_WEXPAND, GLOBALS_TOP, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
    destruct (lib_state_open [] bs m OW PL EA r a LS ND HA ltac:(intros []) NRO) as ((D & BN & ARR) & (OK1 & OK2 & OK3 & OK4) & LSH).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HA) as HV.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS. pose proof PARTS as (WFS & PWF & IDS & PLB & ERRB).
    pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK HA NRO) as (SA0 & SAC & SAI).
    set (b := getbn r bs) in *.
    unfold bn_cells in BN. unfold BG_DMAX in OK3.
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgusegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3346328 - 164) with 3346164 in ERR.
    unfold implM. iprefix.
    destruct (ref_at_ualign s OW LB m bs PL EA r a HEAP PARTS HA NRO) as (PA0 & PA8).
    carve_frame 16%nat ST. do 4 step.
    chk ltac:(fun C => rewrite ?land64_small in C by (clear - PA0 SAC; lia); clear - C PA0 SAC; lia).
    step. rewrite (land7_wrap _ PA8).
    chk ltac:(fun C => clear - C; lia).
    step.
    unfold MallocRep.wz at 1. rewrite (sx32_small (Z.of_nat (bn_dmax b))) by lia.
    step.
    assert (HWL : Forall (w_lib bs OW PL lo (bv_unsigned sp)) [(bv_unsigned sp + -16, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
    assert (WOK : Forall (w_ok OW LB bs PL EA (bv_unsigned sp) []) [(bv_unsigned sp + -16, bv_unsigned sp)]) by (constructor; [apply w_stack; cbn; lia| constructor]).
    if_cases K; zify_cond K; rewrite !signed_small in K by lia.
    -
      do 3 step. release_frame FR ST (bv_unsigned sp). step.
      ihere. to_implM. unfold bn_wexpand, bbind, bget, bret. cbn [bind ret tree_ops tbind fst snd]. fold b.
      replace (words <=? bn_dmax b)%nat with true by (symmetry; apply Nat.leb_le; lia).
      cbn [embed interp]. apply implM_ret. apply evt_done.
      lazymatch goal with |- bn_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mF end.
      unfold bn_post. do 15 eexists. exists mF, OW, PL, errv. split; [reflexivity|]. cbn [fst snd].
      split; [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL)|].
      split; [exact (lib_state_frame s LB _ _ [] bs m mF OW PL EA _ HEAP LS MU WM FROK WOK)|].
      split; [apply (seg_auxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK AUX MU WM HWL SPB ltac:(lia)); unfold GLOBALS_TOP; lia|]. split; [exact ST|].
      split; [unfold LX_ERRNO, RATP; exact ERR|]. split; [exact MI|].
      split; [apply (seg_lx_pres _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL); unfold GLOBALS_TOP; lia|].
      split; [reflexivity|]. split; [reflexivity|]. split; [apply refs_stable_refl|].
      split; [reflexivity|]. split; [reflexivity|]. split; [fold b; lia|]. split; [left; split; [fold b; lia| reflexivity]|]. intros q0 A0 n0 Hq0 _. exact Hq0.
    -
      do 3 step. release_frame FR ST (bv_unsigned sp). step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
      ihere. to_implM.
      eapply implM_mono.
      { eapply (bn_expand2_walk ra sp) with (lo := lo) (B := B) (errv := errv) (r := r) (a := a) (words := words) (OW := OW) (LB := LB) (PL := PL) (EA := EA);
          [| reflexivity | exact HA | exact WR | reflexivity | reflexivity | exact HW].
        unfold bn_pre.
        split; [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL)|].
        split; [exact (lib_state_frame s LB _ _ [] bs m m1 OW PL EA _ HEAP LS MU WM FROK WOK)|]. split; [exact FROK|].
        split; [apply (seg_auxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK AUX MU WM HWL SPB ltac:(lia)); unfold GLOBALS_TOP; lia|]. split; [exact SPB|]. split; [exact B63|].
        split; [exact ST|]. split; [exact CEIL|]. split; [unfold GLOBALS_TOP; lia|]. split; [unfold BN_EXPAND2_STACK; lia|].
        split; [unfold LX_ERRNO, RATP; exact ERR| exact MI]. }
      cbv beta. intros [u bs'] st' ms' PO. unfold bn_post in *. cbn [fst snd] in *.
      destruct PO as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & m' & OW' & PL' & errv' & -> & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11).
      do 15 eexists. exists m', OW', PL', errv'. split; [reflexivity|].
      do 6 (split; [assumption|]). split; [|split; [assumption| split; [assumption| split; [assumption| exact P11]]]].
      eapply lx_pres_trans; [|exact P7]. apply (seg_lx_pres _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL); unfold GLOBALS_TOP; lia.
  Qed.
End Proofs.
End WithCeiling0.
