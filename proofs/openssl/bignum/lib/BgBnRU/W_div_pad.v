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
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BnWordsCorrect BnModel BnTree BnInv BnBridge.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Import Layout Lib_iface Lib_kit F_memset.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnMem BnTacX.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BnDivWords BnDivLoop.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require BnDivSpec.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnArith.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnWU Require Import BnUTac.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnWU Require Import WU_num_bits_word.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr DivLoopPure.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnP Require Import DivLA DivBody DivLoop.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require Import BnHeap DivLA DivBody DivLoop BnAssoc.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require BnRep BnLeaves.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BgState BgInv BgLib.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgRepU Require Import BgRepDefs BgRep BgLayer BgIface BnUAlign.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnRU Require Import BgLeaves W_expand W_ctx BnCall BnRKit W_lshift W_rshift W_ctx_end W_div_tail.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnR Require Import DivModel.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Definition pad_model (snum : bnref) (dn tnp : nat) : bstate bptr -> btree bptr (unit * bstate bptr) :=
  bbind (tree_ops bptr) (bn_wexpand (tree_ops bptr) snum (dn + 1)) (fun _ =>
  bbind (tree_ops bptr) (bget (tree_ops bptr) snum) (fun sn' =>
  bset (tree_ops bptr) snum (mkBN (bn_d sn') (splice (bn_buf sn') tnp (repeat 0 (dn - tnp + 1))) (dn + 1) (bn_neg sn') (bn_flags sn')))).

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Lemma pad_slots : forall m FB (fr1 fr2 fr3 : list cell) (a b : word),
    cells_size fr1 = 112%nat -> cells_size fr2 = 24%nat ->
    rw_cells bgusegs m FB (fr1 ++ C8 a :: fr2 ++ C8 b :: fr3) ->
    rw_cells bgusegs m (FB + 112) [C8 a] /\ rw_cells bgusegs m (FB + 144) [C8 b].
  Proof.
    intros m FB fr1 fr2 fr3 a b S1 S2 H.
    apply bk_rw_cells_app in H. destruct H as [_ H]. rewrite S1 in H. change (Z.of_nat 112) with 112 in H.
    change (C8 a :: fr2 ++ C8 b :: fr3) with ([C8 a] ++ (fr2 ++ C8 b :: fr3)) in H.
    apply bk_rw_cells_app in H. destruct H as [Ha H]. split; [exact Ha|].
    cbn [cells_size csize Nat.add] in H. change (Z.of_nat 8) with 8 in H.
    apply bk_rw_cells_app in H. destruct H as [_ H]. rewrite S2 in H. change (Z.of_nat 24) with 24 in H.
    change (C8 b :: fr3) with ([C8 b] ++ fr3) in H.
    apply bk_rw_cells_app in H. destruct H as [Hb _].
    replace (FB + 144) with (FB + 112 + 8 + 24) by lia. exact Hb.
  Qed.

  Lemma div_pad : forall {Y : Type} (REST : unit -> bstate bptr -> btree bptr (Y * bstate bptr)) (Q : Y * bstate bptr -> PState -> machine_state -> Prop)
      (sp gp : word) (F : bvmap 5 word) (fc : bv 32)
      (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs) (lo B : Z)
      (snum : bnref) (asnum : Z) (fr1 fr2 fr3 : list cell)
      (st8 : PState) (bs8 : bstate bptr) (m8 : mem) (OW8 : list block) (dn tnp : nat)
      (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp + -256 - 16384 -> bv_unsigned sp <= B ->
    frames_ok PL (bv_unsigned sp) B ->
    cells_size fr1 = 112%nat -> cells_size fr2 = 24%nat ->
    cenv LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -256) s bs OW m
      (fr1 ++ C8 (Z_to_bv 64 asnum) :: fr2 ++ C8 (Z_to_bv 64 (Z.of_nat dn)) :: fr3) st8 bs8 m8 OW8 ->
    lib_state bs8 m8 OW8 PL EA ->
    ref_at bs8 OW8 PL snum asnum -> hpl PL snum ->
    bn_top (getbn snum bs8) = tnp -> (tnp <= dn)%nat -> Z.of_nat dn + 1 < 2147483648 ->
    (forall stP bsP mP OWP y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
       cenv LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -256) s bs OW m
         (fr1 ++ C8 (Z_to_bv 64 asnum) :: fr2 ++ C8 (Z_to_bv 64 (Z.of_nat dn)) :: fr3) stP bsP mP OWP ->
       lib_state bsP mP OWP PL EA -> refs_stable bs8 OW8 bsP OWP ->
       (forall r, r <> snum -> getbn r bsP = getbn r bs8) ->
       bn_top (getbn snum bsP) = (dn + 1)%nat -> bn_neg (getbn snum bsP) = bn_neg (getbn snum bs8) ->
       firstn (dn + 1) (bn_buf (getbn snum bsP)) = firstn tnp (bn_buf (getbn snum bs8)) ++ repeat 0 (dn + 1 - tnp) ->
       st_ctx bsP = st_ctx bs8 ->
       implM bgusegs (interp (embed (REST tt bsP))) stP Q
         (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -256)) gp (Z_to_bv 64 RATP) y5 y6 y7 sp (Z_to_bv 64 (Z.of_nat tnp))
                  (Z_to_bv 64 (Z.of_nat dn)) y11 y12 y13 y14 y15 y16 y17 x18 x19 x20 x21 x22 x23 x24 x25 (Z_to_bv 64 (Z.of_nat (dn + 1))) x27 y28 y29 y30 y31)
             F (Z_to_bv 64 0x109a0c) fc None mP (seg_rom bgusegs))) ->
    implM bgusegs (interp (embed (bbind (tree_ops bptr) (pad_model snum dn tnp) REST bs8))) st8 Q
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -256)) gp (Z_to_bv 64 RATP) x5 x6 x7 sp (Z_to_bv 64 (Z.of_nat tnp))
               (Z_to_bv 64 (Z.of_nat dn)) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x10998c) fc None m8 (seg_rom bgusegs)).
  Proof.
    intros until x31. intros CEIL GLO' LO SPB FROK FS1 FS2 ENV8 LS8 HAsn HPs Etop HPAD HDN K.
    pose proof (proj1 HPs) as NROs.
    set (fr := fr1 ++ C8 (Z_to_bv 64 asnum) :: fr2 ++ C8 (Z_to_bv 64 (Z.of_nat dn)) :: fr3) in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (FBlo : lo <= bv_unsigned sp + -256) by lia.
    assert (FBsp : bv_unsigned sp + -256 <= bv_unsigned sp) by lia.
    assert (SPR2 : bv_unsigned sp < 2 ^ 64) by lia.
    pose proof (cenv_pre LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -256) s bs OW m CEIL GLO' FBlo FBsp SPB SPR2 FROK) as CPRE.
    pose proof (cenv_post LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -256) s bs OW m CEIL GLO' FBlo FBsp FROK) as CPOST.
    pose proof (fun A => @bn_post_cpost _ _ LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -256) CEIL FBlo FBsp SPR2 A) as BPC.
    pose proof (cenv_silent LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -256) s bs OW m CEIL GLO' FBlo FBsp SPB FROK) as CSIL.
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS8 HAsn) as HVsn.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS8) as PARTS8; pose proof PARTS8 as (WFS8 & PWF8 & IDS8 & PLB8 & ERRB8).
    pose proof (st_wf_ok snum bs8 WFS8 HVsn NROs) as (OK1 & OK2 & OK3 & OK4).
    destruct (CPRE _ _ _ _ _ BN_WEXPAND_STACK ENV8 LS8 ltac:(unfold BN_WEXPAND_STACK, BN_EXPAND2_STACK; clear - LO; lia)) as (errv9 & PRE9).
    pose proof ENV8 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & FR8 & _).
    destruct (pad_slots _ _ _ _ _ _ _ FS1 FS2 FR8) as (S14 & S18).
    replace (bv_unsigned sp + -256 + 112) with (bv_unsigned sp + -144) in S14 by (clear; lia).
    replace (bv_unsigned sp + -256 + 144) with (bv_unsigned sp + -112) in S18 by (clear; lia).
    unfold implM. iprefix.
    zstep. rewrite (bk_swrap32_small (Z.of_nat dn + 1)) by (clear - HDN; lia).
    zstep. rewrite lts_signed by (clear - HDN; lia). if_cases KO; zify_cond KO. { exfalso. clear - KO. lia. } clear KO.
    step. do 2 zstep.
    clear S14 S18 FR8.
    ihere. to_implM. unfold pad_model. unfold bbind at 1 2. cbn [bind tree_ops].
    apply implM_embed_assoc.
    eapply implM_embed_bind.
    { eapply BnLeaves.implM_embed_leaves; [apply (bn_wexpand_leaves2 snum (dn + 1) bs8 HVsn OK2)|].
      eapply (bn_wexpand_walk HM HF) with (lo := lo) (B := B) (errv := errv9) (r := snum) (a := asnum) (OW := OW8) (LB := LB) (PL := PL) (EA := EA) (words := (dn + 1)%nat);
        [exact PRE9 | reflexivity | exact HAsn | exact (hpl_wref PL snum HPs) | reflexivity | f_equal; f_equal; clear; lia | clear - HDN; lia]. }
    cbv beta. intros [u9 bs9] st9 ms9 [PO LEAF9]. apply BPC in PO.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m9 & OW9 & PL9 & -> & CP9 & (EPL9 & -> & HDM9 & _ & _)).
    subst PL9. specialize (CP9 eq_refl).
    destruct (CPOST _ _ _ _ _ _ _ _ _ ENV8 CP9) as (ENV9 & LS9).
    pose proof (cpost_refs LB PL EA lo B (bv_unsigned sp + -256) _ _ _ _ _ _ _ _ CP9) as RS9.
    cbn [fst snd] in *.
    replace (ret_pc (Z_to_bv 64 1087904)) with (Z_to_bv 64 1087904) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    clear PRE9 CP9.
    destruct LEAF9 as (W1 & W2 & W3 & W4 & W5 & _ & WC & _). cbn [snd] in *. rewrite Etop in W2, W5.

    unfold bbind, bget, bset. cbn [bind ret tree_ops tbind fst snd].
    set (b9 := getbn snum bs9) in *.
    set (k := (dn - tnp + 1)%nat).

    pose proof (ref_at_stable _ _ _ _ _ _ _ RS9 HAsn) as HAsn9.
    pose proof (RH_nodup_l _ _ _ _ (proj1 ENV9)) as ND9.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS9) as PARTS9; pose proof PARTS9 as (WFS9 & PWF9 & IDS9 & PLB9 & ERRB9).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS9 HAsn9) as HVsn9.
    destruct (lib_state_open [] bs9 m9 OW9 PL EA snum asnum LS9 ND9 HAsn9 ltac:(intros []) NROs) as ((D9 & BN9 & ARR9) & (OKa & OKb & OKc & OKd) & LSH9).
    fold b9 in BN9, ARR9, OKa, OKb, OKc, OKd.
    destruct (bn_arr_facts_w bs9 OW9 PL EA (bv_unsigned sp) B st9 LB m9 snum D9 (proj1 ENV9) PARTS9 FROK HVsn9 (hpl_wref PL snum HPs) ARR9) as (U9 & _ & D90 & D9C & D9I & SEP9).
    fold b9 in U9, D9C, D9I, SEP9.
    pose proof (SEP9 snum asnum HAsn9) as SEPs. clear SEP9.
    pose proof (ref_at_hrange _ _ _ _ _ _ _ _ _ (proj1 ENV9) PARTS9 HAsn9 HPs) as (SA0 & SAC & SAI & (qs & As & ns & Hins & Rs1 & Rs2)).
    assert (HD9 : exists p9, bn_d b9 = Some p9 /\ In (p9, D9, 8 * Z.of_nat (bn_dmax b9)) OW9).
    { destruct (bn_d b9) as [p9|] eqn:Ed90; [exists p9; split; [reflexivity|]; unfold bn_arr in ARR9; rewrite Ed90 in ARR9; exact (proj1 ARR9)|].
      exfalso. destruct (bn_arr_null PL snum m9 OW9 D9 b9 PWF9 (hpl_wref PL snum HPs) Ed90 ARR9) as [_ E]. unfold bn_dmax in HDM9. rewrite E in HDM9. cbn in HDM9. lia. }
    destruct HD9 as (p9 & Ed9 & Hinp9).
    unfold bn_cells in BN9. unfold MallocRep.wz in *. unfold BG_DMAX in OKc.
    assert (Lb9 : length (bn_buf b9) = bn_dmax b9) by reflexivity.
    assert (Kk : (tnp + k <= bn_dmax b9)%nat) by (unfold k; clear - HDM9 HPAD; lia).
    assert (Ek : Z.of_nat k = Z.of_nat dn + 1 - Z.of_nat tnp) by (unfold k; clear - HPAD; lia).

    destruct (proj1 (limbarr_split bgusegs m9 D9 (bn_buf b9) tnp ltac:(rewrite Lb9; clear - Kk; lia)) U9) as (Ulo & Urest).
    destruct (proj1 (limbarr_split bgusegs m9 (D9 + 8 * Z.of_nat tnp) (skipn tnp (bn_buf b9)) k ltac:(rewrite length_skipn, Lb9; clear - Kk; lia)) Urest) as (Umid & Uhi).
    clear Urest U9.
    pose proof (limbarr_CB bgusegs m9 _ _ Umid) as CBmid.
    rewrite firstn_length_le in CBmid by (rewrite length_skipn, Lb9; clear - Kk; lia).
    replace (8 * k)%nat with (Z.to_nat (8 * Z.of_nat k)) in CBmid by (clear; lia).
    clear Umid.
    env_open ENV9.
    destruct (pad_slots _ _ _ _ _ _ _ FS1 FS2 FRe) as (S14 & S18).
    replace (bv_unsigned sp + -256 + 112) with (bv_unsigned sp + -144) in S14 by (clear; lia).
    replace (bv_unsigned sp + -256 + 144) with (bv_unsigned sp + -112) in S18 by (clear; lia).
    pose proof (block_ualign _ _ _ _ _ _ _ HEAPe Hinp9) as (D9P & D98).
    match goal with MUx : munch _ m9 m9 |- _ => clear MUx end.
    pose proof (munch_refl [(bv_unsigned sp + -256, bv_unsigned sp); (asnum, asnum + 24); (D9, D9 + 8 * Z.of_nat (bn_dmax b9))]%Z m9) as MU9.
    repeat match goal with H : _ \/ _ |- _ => apply hide_intro in H end.
    unfold implM. iprefix.
    zstep. if_cases KZ; zify_cond KZ. { exfalso. rewrite ?unsigned_lit in KZ by (clear - SA0 Rs1 Rs2 SAC CEIL LO SPR; lia). clear - KZ SA0 Rs1; lia. }
    clear KZ.
    step. step. do 2 zstep.
    replace (D9 + Z.of_nat tnp ≪ 3) with (D9 + 8 * Z.of_nat tnp) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    assert (RNG : 0 <= D9 + 8 * Z.of_nat tnp /\ D9 + 8 * Z.of_nat tnp + 8 * Z.of_nat k <= alloc_ceiling /\ alloc_ceiling <= bv_unsigned sp - 256 - 16384)
      by (clear - D90 D9C Kk CEIL LO; lia).
    do 2 zstep. rewrite ?land64_small by (clear - RNG SPR; lia).
    replace (0 <? D9) with true by (symmetry; apply Z.ltb_lt; exact D9P).
    replace (D9 + 8 * Z.of_nat tnp <? 1) with false by (symmetry; apply Z.ltb_ge; clear - D9P; lia).
    cbn [Z.b2z].
    chk ltac:(fun C => clear - C; lia).
    do 4 zstep.
    rewrite (lxor_signbit63' (Z.of_nat tnp)) by (clear - HPAD HDN; lia).
    replace (Z.of_nat tnp + 9223372036854775808 <? 9223372036854775808) with false by (symmetry; apply Z.ltb_ge; clear; lia).
    replace (D9 + 8 * Z.of_nat tnp <? D9) with false by (symmetry; apply Z.ltb_ge; clear; lia).
    cbn [Z.b2z Z.lxor].
    chk ltac:(fun C => clear - C; lia).
    step. do 2 zstep.
    rewrite (bk_swrap32_small (Z.of_nat dn - Z.of_nat tnp)) by (clear - HDN HPAD; lia).
    replace (Z.of_nat dn + - Z.of_nat tnp) with (Z.of_nat dn - Z.of_nat tnp) by (clear; lia).
    chk ltac:(fun C => clear - C; lia).
    do 2 zstep.
    rewrite (bk_swrap32_small (Z.of_nat dn - Z.of_nat tnp + 1)) by (clear - HDN HPAD; lia).
    rewrite (bk_swrap32_small (Z.of_nat dn - Z.of_nat tnp + 0)) by (clear - HDN HPAD; lia).
    zstep. rewrite lts_signed by (clear - HDN HPAD; lia). if_cases KO; zify_cond KO. { exfalso. clear - KO. lia. } clear KO.
    do 4 zstep.
    replace ((Z.of_nat dn - Z.of_nat tnp + 1) ≪ 3) with (8 * Z.of_nat k) by (rewrite Z.shiftl_mul_pow2 by lia; clear - Ek; lia).
    eapply evt_cut.
    { eapply memset_callZ with (D := D9 + 8 * Z.of_nat tnp) (C := 0) (N := 8 * Z.of_nat k);
        [exact CBmid | match goal with MIx : mem_inv _ m9 |- _ => exact MIx end | clear - RNG; lia | clear - RNG SPR; lia | clear - RNG SPR; lia | clear; lia]. }
    intros ms' PO. unfold memset_postZ in PO.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m10 & E & MUc & WMc & MIc & POST).
    subst ms'.
    replace (ret_pc (Z_to_bv 64 1088000)) with (Z_to_bv 64 1088000) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply hide_elim in SEPs. apply hide_elim in D9I.
    match goal with MIx : mem_inv _ m9 |- _ => clear MIx end. clear CBmid.
    eapply (u64arr_transport bgusegs _ m9 m10) in Ulo; [| exact MUc | exact WMc |
      cbn [disjoint_from]; rewrite wlimbs_len, firstn_length_le by (rewrite Lb9; clear - Kk; lia); split; [left; clear; lia | exact I] ].
    transport_after_call bgusegs m9 m10 MUc WMc.

    change (0 mod 256) with 0 in POST.
    replace (Z.to_nat (8 * Z.of_nat k)) with (8 * k)%nat in POST by (clear; lia).
    rewrite <- lbytes_repeat0 in POST. apply CB_u64arr in POST.
    assert (U10 : u64arr bgusegs m10 D9 (wlimbs (splice (bn_buf b9) tnp (repeat 0 k)))).
    { unfold splice. rewrite repeat_length.
      apply limbarr_app. split; [exact Ulo|]. rewrite firstn_length_le by (rewrite Lb9; clear - Kk; lia).
      apply limbarr_app. split; [exact POST|]. rewrite repeat_length.
      replace (skipn (tnp + k) (bn_buf b9)) with (skipn k (skipn tnp (bn_buf b9))) by (rewrite skipn_skipn; f_equal; clear; lia).
      exact Uhi. }
    clear Ulo Uhi POST.

    apply hide_intro in SEPs. apply hide_intro in D9I. clear MUc WMc.
    pose proof (munch_refl [(asnum, asnum + 24)]%Z m10) as MUa. pose proof (wmono_refl bgusegs m10) as WMa.
    apply hide_intro in ERRe. apply hide_intro in U10.
    step. step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m11 end.
    apply hide_elim in ERRe. apply hide_elim in U10. apply hide_elim in SEPs. apply hide_elim in SAI.
    eapply (rw_cells_transport bgusegs _ m10 m11) in ERRe; [| exact MUa | exact WMa | cbn [disjoint_from cells_size csize Nat.add]; split; [clear - SAI Rs1 Rs2; lia| exact I]].
    eapply (u64arr_transport bgusegs _ m10 m11) in U10; [| exact MUa | exact WMa |
      cbn [disjoint_from]; rewrite wlimbs_len, splice_length by (rewrite repeat_length, Lb9; exact Kk); rewrite Lb9; split; [clear - SEPs; lia | exact I] ].
    clear MUa WMa.

    set (SN := mkBN (bn_d b9) (splice (bn_buf b9) tnp (repeat 0 k)) (dn + 1) (bn_neg b9) (bn_flags b9)).
    assert (Lspl : length (splice (bn_buf b9) tnp (repeat 0 k)) = bn_dmax b9) by (rewrite splice_length by (rewrite repeat_length, Lb9; exact Kk); exact Lb9).
    assert (WOK : Forall (w_ok OW9 LB bs9 PL EA (bv_unsigned sp) [snum]) [(bv_unsigned sp + -256, bv_unsigned sp); (asnum, asnum + 24); (D9, D9 + 8 * Z.of_nat (bn_dmax b9))]).
    { constructor; [apply w_stack; cbn [fst snd]; clear - CEIL LO; lia|].
      constructor; [eapply (w_struct OW9 LB bs9 PL EA (bv_unsigned sp) false [snum] _ snum asnum); [left; reflexivity| exact HAsn9| exact NROs| cbn; lia| cbn; lia]|].
      constructor; [eapply (w_limbs OW9 LB bs9 PL EA (bv_unsigned sp) false [snum] _ snum p9 D9); [left; reflexivity| exact HVsn9| exact Ed9| exact Hinp9| cbn [fst snd]; lia| cbn [fst snd]; fold b9; lia]| constructor]. }
    assert (HWL : Forall (w_lib bs9 OW9 PL lo (bv_unsigned sp)) [(bv_unsigned sp + -256, bv_unsigned sp); (asnum, asnum + 24); (D9, D9 + 8 * Z.of_nat (bn_dmax b9))]).
    { constructor; [left; cbn [fst snd]; clear - LO; lia|]. constructor; [right; left; exists (qs, As, ns); cbn; auto|].
      constructor; [right; left; exists (p9, D9, 8 * Z.of_nat (bn_dmax b9)); cbn; split; [exact Hinp9| lia]| constructor]. }
    assert (LSP : lib_state (setbn snum SN bs9) m11 OW9 PL EA).
    { unfold lib_state. eapply (lib_state_close [] bs9 m11 OW9 PL EA snum asnum); [| exact ND9 | exact HAsn9 | exact NROs | | |].
      - exact (lib_state_frame st9 LB _ _ [snum] bs9 m9 m11 OW9 PL EA _ HEAPe LSH9 MU9 WMe FROK WOK).
      - exists D9. split.
        + unfold bn_cells, SN, bn_dmax, MallocRep.wz. cbn [bn_top bn_buf bn_neg bn_flags]. rewrite Lspl.
          replace (Z.of_nat (dn + 1)) with (Z.of_nat dn + 1) by (clear; lia). exact BN9.
        + unfold bn_arr, SN, bn_dmax. cbn [bn_d bn_buf]. rewrite Ed9, Lspl. split; [exact Hinp9 | exact U10].
      - apply hide_elim in OKd. unfold bg_ok, SN, bn_dmax, BG_DMAX. cbn [bn_top bn_buf bn_flags]. rewrite Lspl.
        split; [apply splice_limbs; [exact OKa | apply limbs_repeat; exact limb_0]|]. split; [exact HDM9|]. split; [exact OKc| exact OKd].
      - apply ids_ok_setbn_same; [exact IDS9 | exact HVsn9 |]. fold b9. unfold bn_blocks, SN, bn_dmax. cbn [bn_d bn_buf]. rewrite Lspl. reflexivity. }
    assert (ENVP : cenv LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -256) s bs OW m fr st9 (setbn snum SN bs9) m11 OW9).
    { apply cenv_setbn. destruct ENV8 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FSZ8).
      eapply (CSIL _ fr); [exact ENV9 | exact LS9 | exact MU9 | exact WMe | exact HWL | exact STe | unfold LX_ERRNO, RATP; exact ERRe | exact MIc | exact FRe | exact FSZ8]. }
    ihere. to_implM.
    replace (Z.of_nat dn + 1) with (Z.of_nat (dn + 1)) by (clear; lia).
    eapply K; [exact ENVP | exact LSP | | | | | |].
    - eapply refs_stable_trans; [exact RS9| apply refs_stable_setbn].
    - intros r0 Hr0. rewrite getbn_setbn_other by (apply not_eq_sym; exact Hr0). apply W1. apply not_eq_sym. exact Hr0.
    - rewrite getbn_setbn_same by exact HVsn9. reflexivity.
    - rewrite getbn_setbn_same by exact HVsn9. cbn [SN bn_neg]. exact W3.
    - rewrite getbn_setbn_same by exact HVsn9. cbn [SN bn_buf].
      replace (dn + 1)%nat with (tnp + k)%nat by (unfold k; clear - HPAD; lia).
      rewrite BnDivSpec.firstn_pad_zeros by (rewrite Lb9; exact Kk). rewrite W5.
      replace (tnp + k - tnp)%nat with k by (clear; lia). reflexivity.
    - rewrite st_ctx_setbn. exact WC.
  Qed.
End Proofs.
End WithCeiling0.
