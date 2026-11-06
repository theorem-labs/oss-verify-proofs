(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OSSVerify.Proofs.openssl.bndiv.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.openssl.bndiv.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import BnBase BnWords BnWordsCorrect BnModel BnTree BnInv BnSpecs BnMInv BnBridge.
From OSSVerify.Proofs.openssl.bndiv.lib.U Require Import Layout Lib_iface Lib_kit F_memset.
From OSSVerify.Proofs.openssl.bndiv.lib.BnW Require Import BnTac BnMem BnTacX.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import BnDivWords BnDivLoop BnSpecs2 BnDivSpec.
From OSSVerify.Proofs.openssl.bndiv.lib.BnW Require Import BnArith.
From OSSVerify.Proofs.openssl.bndiv.lib.BnWU Require Import BnUTac.
From OSSVerify.Proofs.openssl.bndiv.lib.BnP Require Import BnKit BnKit2 BnArr DivModel.
From OSSVerify.Proofs.openssl.bndiv.lib.BnU Require Import BnHeap BnRep BnIface W_expand BnLeaves BnUAlign BnCall BnAssoc W_div_tail.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.openssl.bndiv.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].






(* [comment removed for export] *)
Definition pad_model (snum : bnref) (dn tnp : nat) : lstate bptr -> btree bptr (unit * lstate bptr) :=
  bbind (tree_ops bptr) (bn_wexpand (tree_ops bptr) snum (dn + 1)) (fun _ =>
  bbind (tree_ops bptr) (bget (tree_ops bptr) snum) (fun sn' =>
  bset (tree_ops bptr) snum (mkBN (bn_d sn') (splice (bn_buf sn') tnp (repeat 0 (dn - tnp + 1))) (dn + 1) (bn_neg sn') (bn_flags sn')))).

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  (* [comment removed for export] *)
  Lemma pad_slots : forall m FB (fr1 fr2 fr3 : list cell) (a b : word),
    cells_size fr1 = 112%nat -> cells_size fr2 = 24%nat ->
    rw_cells usegs m FB (fr1 ++ C8 a :: fr2 ++ C8 b :: fr3) ->
    rw_cells usegs m (FB + 112) [C8 a] /\ rw_cells usegs m (FB + 144) [C8 b].
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

  Lemma div_pad : forall {Y : Type} (REST : unit -> lstate bptr -> btree bptr (Y * lstate bptr)) (Q : Y * lstate bptr -> PState -> machine_state -> Prop)
      (sp gp : word) (F : bvmap 5 word) (fc : bv 32)
      (m : mem) (s : PState) (ls : lstate bptr) (OW LB : list block) (AD : bn_addrs) (EA : err_addrs) (lo B : Z)
      (snum : bnref) (asnum : Z) (fr1 fr2 fr3 : list cell)
      (st8 : PState) (ls8 : lstate bptr) (m8 : mem) (OW8 : list block) (dn tnp : nat)
      (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp + -256 - 16384 -> bv_unsigned sp <= B ->
    cells_size fr1 = 112%nat -> cells_size fr2 = 24%nat ->
    cenv LB AD lo B (bv_unsigned sp) (bv_unsigned sp + -256) s ls OW m
      (fr1 ++ C8 (Z_to_bv 64 asnum) :: fr2 ++ C8 (Z_to_bv 64 (Z.of_nat dn)) :: fr3) st8 ls8 m8 OW8 ->
    lib_state ls8 m8 OW8 AD EA ->
    ref_at ls8 OW8 AD snum asnum ->
    bn_top (getbn snum ls8) = tnp -> (tnp <= dn)%nat -> Z.of_nat dn + 1 < 2147483648 ->
    (forall stP lsP mP OWP y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
       cenv LB AD lo B (bv_unsigned sp) (bv_unsigned sp + -256) s ls OW m
         (fr1 ++ C8 (Z_to_bv 64 asnum) :: fr2 ++ C8 (Z_to_bv 64 (Z.of_nat dn)) :: fr3) stP lsP mP OWP ->
       lib_state lsP mP OWP AD EA -> refs_stable ls8 OW8 lsP OWP AD ->
       (forall r, r <> snum -> getbn r lsP = getbn r ls8) ->
       bn_top (getbn snum lsP) = (dn + 1)%nat -> bn_neg (getbn snum lsP) = bn_neg (getbn snum ls8) ->
       firstn (dn + 1) (bn_buf (getbn snum lsP)) = firstn tnp (bn_buf (getbn snum ls8)) ++ repeat 0 (dn + 1 - tnp) ->
       implM usegs (interp (embed (REST tt lsP))) stP Q
         (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -256)) gp (Z_to_bv 64 RATP) y5 y6 y7 sp (Z_to_bv 64 (Z.of_nat tnp))
                  (Z_to_bv 64 (Z.of_nat dn)) y11 y12 y13 y14 y15 y16 y17 x18 x19 x20 x21 x22 x23 x24 x25 (Z_to_bv 64 (Z.of_nat (dn + 1))) x27 y28 y29 y30 y31)
             F (Z_to_bv 64 0x119638) fc None mP (seg_rom usegs))) ->
    implM usegs (interp (embed (bbind (tree_ops bptr) (pad_model snum dn tnp) REST ls8))) st8 Q
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -256)) gp (Z_to_bv 64 RATP) x5 x6 x7 sp (Z_to_bv 64 (Z.of_nat tnp))
               (Z_to_bv 64 (Z.of_nat dn)) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x1195b8) fc None m8 (seg_rom usegs)).
  Proof.
    intros until x31. intros CEIL GLO' LO SPB FS1 FS2 ENV8 LS8 HAsn Etop HPAD HDN K.
    set (fr := fr1 ++ C8 (Z_to_bv 64 asnum) :: fr2 ++ C8 (Z_to_bv 64 (Z.of_nat dn)) :: fr3) in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (FBlo : lo <= bv_unsigned sp + -256) by lia.
    assert (FBsp : bv_unsigned sp + -256 <= bv_unsigned sp) by lia.
    assert (SPR2 : bv_unsigned sp < 2 ^ 64) by lia.
    pose proof (cenv_pre LB AD EA lo B (bv_unsigned sp) (bv_unsigned sp + -256) s ls OW m CEIL GLO' FBlo FBsp SPB SPR2) as CPRE.
    pose proof (cenv_post LB AD EA lo B (bv_unsigned sp) (bv_unsigned sp + -256) s ls OW m CEIL GLO' FBlo FBsp) as CPOST.
    pose proof (fun A => @bn_post_cpost _ _ LB AD EA lo B (bv_unsigned sp) (bv_unsigned sp + -256) CEIL FBlo FBsp SPR2 A) as BPC.
    pose proof (cenv_silent LB AD lo B (bv_unsigned sp) (bv_unsigned sp + -256) s ls OW m CEIL GLO' FBlo FBsp SPB) as CSIL.
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS8 HAsn) as HVsn.
    destruct (lib_state_h_parts _ _ _ _ _ _ LS8) as (IDS8 & ADB8 & ERRB8 & SOK8).
    pose proof (st_okm_getbn snum ls8 SOK8 HVsn) as (OK1 & OK2 & OK3 & OK4).
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
    { eapply implM_embed_leaves; [apply (bn_wexpand_leaves2 snum (dn + 1) ls8 HVsn OK2)|].
      eapply (bn_wexpand_walk HM HF) with (lo := lo) (B := B) (errv := errv9) (r := snum) (a := asnum) (OW := OW8) (LB := LB) (AD := AD) (EA := EA);
        [exact PRE9 | reflexivity | exact HAsn | reflexivity | f_equal; f_equal; clear; lia | clear - HDN; lia]. }
    cbv beta. intros [u9 ls9] st9 ms9 [PO LEAF9]. apply BPC in PO.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m9 & OW9 & -> & CP9 & (-> & HDM9 & _ & _)).
    destruct (CPOST _ _ _ _ _ _ _ _ _ ENV8 CP9) as (ENV9 & LS9).
    pose proof (cpost_refs LB AD EA lo B (bv_unsigned sp + -256) _ _ _ _ _ _ _ _ CP9) as RS9.
    cbn [fst snd] in *.
    replace (ret_pc (Z_to_bv 64 1152460)) with (Z_to_bv 64 1152460) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    clear PRE9 CP9.
    destruct LEAF9 as ((W1 & W2 & W3 & W4 & W5) & _ & _). cbn [snd] in *. rewrite Etop in W2, W5.
    (* [comment removed for export] *)
    unfold bbind, bget, bset. cbn [bind ret tree_ops tbind fst snd].
    set (b9 := getbn snum ls9) in *.
    set (k := (dn - tnp + 1)%nat).
    (* [comment removed for export] *)
    pose proof (RS9 _ _ HAsn) as HAsn9.
    pose proof (RH_nodup_l _ _ _ _ (proj1 ENV9)) as ND9.
    destruct (lib_state_h_parts _ _ _ _ _ _ LS9) as (IDS9 & ADB9 & ERRB9 & SOK9).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS9 HAsn9) as HVsn9.
    destruct (lib_state_open [] ls9 m9 OW9 AD EA snum asnum LS9 ND9 HAsn9 ltac:(intros [])) as ((D9 & BN9 & ARR9) & (OKa & OKb & OKc & OKd) & LSH9).
    fold b9 in BN9, ARR9, OKa, OKb, OKc, OKd.
    destruct (bn_arr_facts st9 OW9 LB m9 (proj1 ENV9) ls9 AD EA IDS9 ADB9 snum D9 HVsn9 ARR9) as (U9 & _ & D90 & D9C & D9I & SEP9).
    fold b9 in U9, D9C, D9I, SEP9.
    pose proof (SEP9 snum asnum HAsn9) as SEPs. clear SEP9.
    destruct (ref_at_inb _ _ _ _ _ ADB9 HAsn9) as (qs & As & ns & _ & Hins & Rs1 & Rs2).
    pose proof (RH_range _ _ _ _ _ _ _ (proj1 ENV9) Hins) as (SA0 & _ & _ & SAC & SAI).
    assert (HD9 : exists p9, bn_d b9 = Some p9 /\ In (p9, D9, 8 * Z.of_nat (bn_dmax b9)) OW9).
    { unfold bn_arr in ARR9. destruct (bn_d b9) as [p9|]; [exists p9; split; [reflexivity| exact (proj1 ARR9)]|].
      exfalso. destruct ARR9 as [_ E]. unfold bn_dmax in HDM9. rewrite E in HDM9. cbn in HDM9. lia. }
    destruct HD9 as (p9 & Ed9 & Hinp9).
    unfold bn_cells in BN9. unfold MallocRep.wz in *. unfold BN_WORDS_MAX in OKc.
    assert (Lb9 : length (bn_buf b9) = bn_dmax b9) by reflexivity.
    assert (Kk : (tnp + k <= bn_dmax b9)%nat) by (unfold k; clear - HDM9 HPAD; lia).
    assert (Ek : Z.of_nat k = Z.of_nat dn + 1 - Z.of_nat tnp) by (unfold k; clear - HPAD; lia).
    (* [comment removed for export] *)
    destruct (proj1 (limbarr_split usegs m9 D9 (bn_buf b9) tnp ltac:(rewrite Lb9; clear - Kk; lia)) U9) as (Ulo & Urest).
    destruct (proj1 (limbarr_split usegs m9 (D9 + 8 * Z.of_nat tnp) (skipn tnp (bn_buf b9)) k ltac:(rewrite length_skipn, Lb9; clear - Kk; lia)) Urest) as (Umid & Uhi).
    clear Urest U9.
    pose proof (limbarr_CB usegs m9 _ _ Umid) as CBmid.
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
    (* [comment removed for export] *)
    replace ((Z.of_nat dn - Z.of_nat tnp + 1) ≪ 3) with (8 * Z.of_nat k) by (rewrite Z.shiftl_mul_pow2 by lia; clear - Ek; lia).
    eapply evt_cut.
    { eapply memset_callZ with (D := D9 + 8 * Z.of_nat tnp) (C := 0) (N := 8 * Z.of_nat k);
        [exact CBmid | match goal with MIx : mem_inv _ m9 |- _ => exact MIx end | clear - RNG; lia | clear - RNG SPR; lia | clear - RNG SPR; lia | clear; lia]. }
    intros ms' PO. unfold memset_postZ in PO.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m10 & E & MUc & WMc & MIc & POST).
    subst ms'.
    replace (ret_pc (Z_to_bv 64 1152556)) with (Z_to_bv 64 1152556) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply hide_elim in SEPs. apply hide_elim in D9I.
    match goal with MIx : mem_inv _ m9 |- _ => clear MIx end. clear CBmid.
    eapply (u64arr_transport usegs _ m9 m10) in Ulo; [| exact MUc | exact WMc |
      cbn [disjoint_from]; rewrite wlimbs_len, firstn_length_le by (rewrite Lb9; clear - Kk; lia); split; [left; clear; lia | exact I] ].
    transport_after_call usegs m9 m10 MUc WMc.
    (* [comment removed for export] *)
    change (0 mod 256) with 0 in POST.
    replace (Z.to_nat (8 * Z.of_nat k)) with (8 * k)%nat in POST by (clear; lia).
    rewrite <- lbytes_repeat0 in POST. apply CB_u64arr in POST.
    assert (U10 : u64arr usegs m10 D9 (wlimbs (splice (bn_buf b9) tnp (repeat 0 k)))).
    { unfold splice. rewrite repeat_length.
      apply limbarr_app. split; [exact Ulo|]. rewrite firstn_length_le by (rewrite Lb9; clear - Kk; lia).
      apply limbarr_app. split; [exact POST|]. rewrite repeat_length.
      replace (skipn (tnp + k) (bn_buf b9)) with (skipn k (skipn tnp (bn_buf b9))) by (rewrite skipn_skipn; f_equal; clear; lia).
      exact Uhi. }
    clear Ulo Uhi POST.
    (* [comment removed for export] *)
    apply hide_intro in SEPs. apply hide_intro in D9I. clear MUc WMc.
    pose proof (munch_refl [(asnum, asnum + 24)]%Z m10) as MUa. pose proof (wmono_refl usegs m10) as WMa.
    apply hide_intro in ERRe. apply hide_intro in U10.
    step. step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m11 end.
    apply hide_elim in ERRe. apply hide_elim in U10. apply hide_elim in SEPs. apply hide_elim in SAI.
    eapply (rw_cells_transport usegs _ m10 m11) in ERRe; [| exact MUa | exact WMa | cbn [disjoint_from cells_size csize Nat.add]; split; [clear - SAI Rs1 Rs2; lia| exact I]].
    eapply (u64arr_transport usegs _ m10 m11) in U10; [| exact MUa | exact WMa |
      cbn [disjoint_from]; rewrite wlimbs_len, splice_length by (rewrite repeat_length, Lb9; exact Kk); rewrite Lb9; split; [clear - SEPs; lia | exact I] ].
    clear MUa WMa.
    (* [comment removed for export] *)
    set (SN := mkBN (bn_d b9) (splice (bn_buf b9) tnp (repeat 0 k)) (dn + 1) (bn_neg b9) (bn_flags b9)).
    assert (Lspl : length (splice (bn_buf b9) tnp (repeat 0 k)) = bn_dmax b9) by (rewrite splice_length by (rewrite repeat_length, Lb9; exact Kk); exact Lb9).
    assert (WOK : Forall (w_ok OW9 LB ls9 AD EA [snum]) [(bv_unsigned sp + -256, bv_unsigned sp); (asnum, asnum + 24); (D9, D9 + 8 * Z.of_nat (bn_dmax b9))]).
    { constructor; [apply w_stack; cbn [fst]; clear - CEIL LO; lia|].
      constructor; [eapply (w_struct OW9 LB ls9 AD EA false [snum] _ snum asnum); [left; reflexivity| exact HAsn9| cbn; lia| cbn; lia]|].
      constructor; [eapply (w_limbs OW9 LB ls9 AD EA false [snum] _ snum p9 D9); [left; reflexivity| exact HVsn9| exact Ed9| exact Hinp9| cbn [fst snd]; lia| cbn [fst snd]; fold b9; lia]| constructor]. }
    assert (HWL : Forall (w_lib OW9 lo (bv_unsigned sp)) [(bv_unsigned sp + -256, bv_unsigned sp); (asnum, asnum + 24); (D9, D9 + 8 * Z.of_nat (bn_dmax b9))]).
    { constructor; [left; cbn [fst snd]; clear - LO; lia|]. constructor; [right; exists (qs, As, ns); cbn; auto|].
      constructor; [right; exists (p9, D9, 8 * Z.of_nat (bn_dmax b9)); cbn; split; [exact Hinp9| lia]| constructor]. }
    assert (LSP : lib_state (setbn snum SN ls9) m11 OW9 AD EA).
    { unfold lib_state. eapply (lib_state_close [] ls9 m11 OW9 AD EA snum asnum); [| exact ND9 | exact HAsn9 | | |].
      - exact (lib_state_frame st9 LB [snum] ls9 m9 m11 OW9 AD EA _ HEAPe LSH9 MU9 WMe WOK).
      - exists D9. split.
        + unfold bn_cells, SN, bn_dmax, MallocRep.wz. cbn [bn_top bn_buf bn_neg bn_flags]. rewrite Lspl.
          replace (Z.of_nat (dn + 1)) with (Z.of_nat dn + 1) by (clear; lia). exact BN9.
        + unfold bn_arr, SN, bn_dmax. cbn [bn_d bn_buf]. rewrite Ed9, Lspl. split; [exact Hinp9 | exact U10].
      - apply hide_elim in OKd. unfold bn_okm, SN, bn_dmax, BN_WORDS_MAX. cbn [bn_top bn_buf bn_flags]. rewrite Lspl.
        split; [apply splice_limbs; [exact OKa | apply limbs_repeat; exact limb_0]|]. split; [exact HDM9|]. split; [exact OKc| exact OKd].
      - apply ids_ok_setbn_same; [exact IDS9 | exact HVsn9 |]. fold b9. unfold bn_blocks, SN, bn_dmax. cbn [bn_d bn_buf]. rewrite Lspl. reflexivity. }
    assert (ENVP : cenv LB AD lo B (bv_unsigned sp) (bv_unsigned sp + -256) s ls OW m fr st9 (setbn snum SN ls9) m11 OW9).
    { apply cenv_setbn. destruct ENV8 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FSZ8).
      eapply (CSIL _ fr); [exact ENV9 | exact MU9 | exact WMe | exact HWL | exact STe | unfold LX_ERRNO, RATP; exact ERRe | exact MIc | exact FRe | exact FSZ8]. }
    ihere. to_implM.
    replace (Z.of_nat dn + 1) with (Z.of_nat (dn + 1)) by (clear; lia).
    eapply K; [exact ENVP | exact LSP | | | | |].
    - intros r0 a0 H0. apply ref_at_setbn. apply RS9. exact H0.
    - intros r0 Hr0. rewrite getbn_setbn_other by (apply not_eq_sym; exact Hr0). apply W1. apply not_eq_sym. exact Hr0.
    - rewrite getbn_setbn_same_m by exact HVsn9. reflexivity.
    - rewrite getbn_setbn_same_m by exact HVsn9. cbn [SN bn_neg]. exact W3.
    - rewrite getbn_setbn_same_m by exact HVsn9. cbn [SN bn_buf].
      replace (dn + 1)%nat with (tnp + k)%nat by (unfold k; clear - HPAD; lia).
      rewrite firstn_pad_zeros by (rewrite Lb9; exact Kk). rewrite W5.
      replace (tnp + k - tnp)%nat with k by (clear; lia). reflexivity.
  Qed.
End Proofs.
End WithCeiling0.
