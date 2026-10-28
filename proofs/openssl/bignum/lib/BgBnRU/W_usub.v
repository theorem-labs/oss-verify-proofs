(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.

From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BnWordsCorrect BnModel BnTree BnInv BnSpecs BnAddSpec BnMInv BnBridge BgState BgInv BgLib.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Import Layout Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnMem BnTacX.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnWU Require Import BnUTac.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnA Require Import W_usub_core.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require Import BnHeap.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require BnRep BnLeaves.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgRepU Require Import BgRepDefs BgRep BgLayer BgIface BnUAlign.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnA Require Import BnAPure.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnAU Require Import BnAKit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnRU Require Import W_expand BnCall BnRKit W_usub_core W_uadd.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Local Notation ops := (tree_ops bptr).

Definition usub_rest (rr x y : bnref) (max min : nat) : BM (M := btree bptr) unit :=
  bbind ops (if (max =? 0)%nat then bret ops tt
             else bbind ops (bget ops x) (fun a => bbind ops (bget ops y) (fun b => bbind ops (bget ops rr) (fun r =>
                  let '(s, borrow) := sub_words (firstn min (bn_buf a)) (firstn min (bn_buf b)) in
                  let '(s2, _) := sub_part_pos (slice (bn_buf a) min (max - min)) borrow in
                  bset ops rr (bn_with_buf r (splice (bn_buf r) 0 (s ++ s2)))))))
    (fun _ => bbind ops (bget ops rr) (fun r => bset ops rr (mkBN (bn_d r) (bn_buf r) (strip_top (bn_buf r) max) false (bn_flags r)))).

Lemma BN_usub_eq : forall rr x y (bs : bstate bptr),
  BN_usub ops rr x y bs =
  if (bn_top (getbn x bs) <? bn_top (getbn y bs))%nat then TUnr
  else tbind (bn_wexpand ops rr (bn_top (getbn x bs)) bs) (fun p => usub_rest rr x y (bn_top (getbn x bs)) (bn_top (getbn y bs)) (snd p)).
Proof.
  intros rr x y bs. unfold BN_usub, bbind at 1 2. cbn [bind tree_ops bget tbind ret fst snd].
  destruct (bn_top (getbn x bs) <? bn_top (getbn y bs))%nat; reflexivity.
Qed.

Lemma usub_rest_eq : forall rr x y (bs : bstate bptr) max min,
  vref rr bs -> (min <= max)%nat -> (max <= length (bn_buf (getbn x bs)))%nat -> (min <= length (bn_buf (getbn y bs)))%nat ->
  usub_rest rr x y max min bs =
  TRet (tt, setbn rr (usub_bn (getbn rr bs) (firstn max (bn_buf (getbn x bs))) (firstn min (bn_buf (getbn y bs)))) bs).
Proof.
  intros rr x y bs max min HV Hmm Hx Hy.
  unfold usub_rest, bbind, bget, bset, bret. cbn [bind ret tree_ops tbind fst snd].
  assert (LA : length (firstn max (bn_buf (getbn x bs))) = max) by (apply firstn_length_le; exact Hx).
  assert (LB : length (firstn min (bn_buf (getbn y bs))) = min) by (apply firstn_length_le; exact Hy).
  unfold usub_bn, usub_top, usub_buf. rewrite LA.
  destruct (Nat.eqb_spec max 0) as [E0|N0].
  - cbn [tbind fst snd]. rewrite E0. reflexivity.
  - rewrite (slice_of_firstn (bn_buf (getbn x bs)) min max Hmm).
    unfold usub_list. rewrite LB. rewrite firstn_firstn, Nat.min_l by exact Hmm.
    destruct (sub_words (firstn min (bn_buf (getbn x bs))) (firstn min (bn_buf (getbn y bs)))) as [sv cv].
    destruct (sub_part_pos (skipn min (firstn max (bn_buf (getbn x bs)))) cv) as [sv2 cv2].
    cbn [tbind fst snd]. rewrite !getbn_setbn_same by exact HV. rewrite !setbn_setbn_same.
    unfold bn_with_buf. cbn [bn_d bn_buf bn_top bn_neg bn_flags fst snd]. reflexivity.
Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition BN_USUB : Z := 0x10aa0c.
Definition BN_USUB_STACK : Z := 64 + BN_WEXPAND_STACK.

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Lemma BN_usub_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (rr x y : bnref) (R X Y : Z),
    bn_pre s bs m OW LB PL EA sp lo B errv BN_USUB_STACK -> tp = wz RATP ->
    ref_at bs OW PL rr R -> hpl PL rr -> ref_at bs OW PL x X -> x <> ROne -> ref_at bs OW PL y Y -> y <> ROne ->
    a0 = wz R -> a1 = wz X -> a2 = wz Y ->
    implM bgusegs (interp (embed (BN_usub (tree_ops bptr) rr x y bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (uarith_res rr bs OW PL))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_USUB) fc None m (seg_rom bgusegs)).
  Proof.
    intros until Y. intros PRE -> HR HP HX NX HY NY -> -> ->. pose proof (proj1 HP) as NRO.
    pose proof PRE as (HEAP & LS & FROK & AUX & SPB & B63 & ST & CEIL & GLO & LO & ERR & MI).
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
    unfold BN_USUB_STACK, BN_WEXPAND_STACK, BN_EXPAND2_STACK in LO.
    unfold BN_USUB, MallocRep.wz.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    destruct (open_ro_u s OW LB m bs PL EA (bv_unsigned sp) B x X HEAP LS FROK HX NX) as (Dx0 & SX & OKX & _ & X0 & XC & _ & _ & ALX0 & _).
    destruct (open_ro_u s OW LB m bs PL EA (bv_unsigned sp) B y Y HEAP LS FROK HY NY) as (Dy0 & SY & OKY & _ & Y0 & YC & _ & _ & ALY0 & _).
    pose proof OKX as (_ & TDX & DMX & _). pose proof OKY as (_ & TDY & DMY & _). unfold BG_DMAX in DMX, DMY.
    unfold bn_cells, MallocRep.wz in SX, SY.
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgusegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3346328 - 164) with 3346164 in ERR.
    assert (GLO' : GLOBALS_TOP <= lo) by exact GLO. unfold GLOBALS_TOP in GLO.
    rewrite BN_usub_eq.
    set (max := bn_top (getbn x bs)) in *. set (min := bn_top (getbn y bs)) in *.
    unfold implM. iprefix.
    carve_frame 64%nat ST. do 10 zstep.
    chk ltac:(fun C => clear - C X0; lia).
    do 3 zstep. rewrite (land7 X (hide_elim _ ALX0)). chk_lit.
    zstep.
    chk ltac:(fun C => clear - C Y0; lia).
    zstep. rewrite (land7 Y (hide_elim _ ALY0)). chk_lit.
    zstep. rewrite (sx32_small (Z.of_nat max)) by (clear - TDX DMX; unfold bn_dmax in *; lia).
    zstep. rewrite (sx32_small (Z.of_nat min)) by (clear - TDY DMY; unfold bn_dmax in *; lia).
    zstep. rewrite (bn_swrap32_small (Z.of_nat max - Z.of_nat min)) by (clear - TDX DMX TDY DMY; unfold bn_dmax in *; lia).
    zstep. replace (Z.of_nat max + - Z.of_nat min)%Z with (Z.of_nat max - Z.of_nat min)%Z by (clear; lia).
    chk ltac:(fun C => clear - C; lia).
    zstep. rewrite lts_signed by (clear - TDX DMX TDY DMY; unfold bn_dmax in *; lia).
    if_cases K; zify_cond K.
    {
      replace (max <? min)%nat with true by (symmetry; apply Nat.ltb_lt; clear - K; lia).
      ihere. to_implM. cbn [embed interp]. apply implM_interp_unr. }
    replace (max <? min)%nat with false by (symmetry; apply Nat.ltb_ge; clear - K; lia).
    assert (HTOPS : (min <= max)%nat) by (clear - K; lia). clear K.
    do 3 zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HWL0 : Forall (w_lib bs OW PL lo (bv_unsigned sp)) [(bv_unsigned sp + -64, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
    assert (WOK0 : Forall (w_ok OW LB bs PL EA (bv_unsigned sp) []) [(bv_unsigned sp + -64, bv_unsigned sp)]) by (constructor; [apply w_stack; cbn; lia| constructor]).
    pose proof (lib_state_frame s LB _ _ [] bs m m1 OW PL EA _ HEAP LS MU WM FROK WOK0) as LS0.
    lazymatch type of FR with rw_cells _ _ _ ?fr =>
      assert (ENV : cenv LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -64) s bs OW m fr s bs m1 OW)
    end.
    { unfold cenv. split; [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL0 CEIL)|].
      split; [apply (seg_auxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK AUX MU WM HWL0 SPB ltac:(lia)); exact GLO'|].
      split; [exact ST|]. split; [exists errv; unfold LX_ERRNO, RATP; exact ERR|]. split; [exact MI|].
      split; [apply (seg_lx_pres _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL0 CEIL); [exact GLO'| lia]|].
      split; [reflexivity|]. split; [reflexivity|]. split; [apply refs_stable_refl|]. split; [exact FR| cbn; lia]. }
    assert (FBlo : lo <= bv_unsigned sp + -64) by lia.
    assert (FBsp : bv_unsigned sp + -64 <= bv_unsigned sp) by lia.
    assert (SPR2 : bv_unsigned sp < 2 ^ 64) by lia.
    pose proof (cenv_pre LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -64) s bs OW m CEIL GLO' FBlo FBsp SPB SPR2 FROK) as CPRE.
    pose proof (cenv_post LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -64) s bs OW m CEIL GLO' FBlo FBsp FROK) as CPOST.
    pose proof (fun A => @bn_post_cpost _ _ LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -64) CEIL FBlo FBsp SPR2 A) as BPC.
    clear HEAP LS AUX ST ERR MI MU WM HWL0 WOK0 FR PRE SX SY.

    destruct (CPRE _ _ _ _ _ BN_WEXPAND_STACK ENV LS0 ltac:(unfold BN_WEXPAND_STACK, BN_EXPAND2_STACK; lia)) as (errv1 & PRE1).
    ihere. to_implM.
    eapply implM_embed_bind.
    { eapply (bn_wexpand_walk HM HF) with (lo := lo) (B := B) (errv := errv1) (OW := OW) (LB := LB) (PL := PL) (EA := EA)
        (r := rr) (a := R) (words := max);
        [exact PRE1 | reflexivity | exact HR | exact (hpl_wref PL rr HP) | reflexivity | reflexivity | clear - TDX DMX; unfold bn_dmax in *; lia]. }
    cbv beta. intros [u1 bs1] st1 ms1 PO. apply BPC in PO.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m2 & OW1 & PL1 & -> & CP & (EPL & -> & HDM & WRES & STAB)).
    subst PL1. specialize (CP eq_refl).
    destruct (CPOST _ _ _ _ _ _ _ _ _ ENV CP) as (ENV1 & LS1).
    pose proof (cpost_refs LB PL EA lo B (bv_unsigned sp + -64) _ _ _ _ _ _ _ _ CP) as RS.
    cbn [fst snd] in *.
    replace (ret_pc (Z_to_bv 64 1092220)) with (Z_to_bv 64 1092220) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (ref_at_stable _ _ _ _ _ _ _ RS HR) as HR1. pose proof (ref_at_stable _ _ _ _ _ _ _ RS HX) as HX1. pose proof (ref_at_stable _ _ _ _ _ _ _ RS HY) as HY1.
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS0 HR) as HVR.
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS1 HR1) as HVR1.
    assert (ETX : bn_top (getbn x bs1) = max) by (apply (wexpand_res_top rr max bs bs1 x WRES HVR)).
    assert (ETY : bn_top (getbn y bs1) = min) by (apply (wexpand_res_top rr max bs bs1 y WRES HVR)).
    clear OKX OKY TDX TDY Dx0 Dy0 PRE1 CP LS0 ENV.

    pose proof ENV1 as (HEAP2 & AUX2 & ST2 & (errv2 & ERR2) & MI2 & LXP2 & FA2 & SO2 & _ & FR2 & _).
    pose proof (RH_nodup_l _ _ _ _ HEAP2) as ND2.
    destruct (lib_state_open [] bs1 m2 OW1 PL EA rr R LS1 ND2 HR1 ltac:(intros []) NRO) as ((Dr & SR & ARR) & OKR' & LSH). pose proof (bg_okm _ OKR') as OKR.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS1) as PARTS1; pose proof PARTS1 as (WFS1 & PWF1 & IDS1 & PLB1 & ERRB1).
    destruct (bn_arr_facts_w bs1 OW1 PL EA (bv_unsigned sp) B st1 LB m2 rr Dr HEAP2 PARTS1 FROK HVR1 (hpl_wref PL rr HP) ARR) as (UR & LENR & DR0 & DRC & _ & DSEPR).
    pose proof (ref_at_hrange _ _ _ _ _ _ _ _ _ HEAP2 PARTS1 HR1 HP) as (SA0 & SAC & SAI & (qs & As & ns & Hins & Ra1 & Ra2)).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS1 HX1) as HVX1. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS1 HY1) as HVY1.
    pose proof (st_wf_ok x bs1 WFS1 HVX1 NX) as (LMX & TDX & _). pose proof (st_wf_ok y bs1 WFS1 HVY1 NY) as (LMY & TDY & _).
    destruct (operand_view_u st1 OW1 LB m2 bs1 PL EA (bv_unsigned sp) B rr R Dr x X max HEAP2 LS1 FROK HR1 HP SR ARR HX1 NX ltac:(rewrite ETX; lia))
      as (Dx & HXd & HLX & X0' & XC' & DX0 & DXC & SXR & SXA & ALX & UPX & _).
    destruct (operand_view_u st1 OW1 LB m2 bs1 PL EA (bv_unsigned sp) B rr R Dr y Y min HEAP2 LS1 FROK HR1 HP SR ARR HY1 NY ltac:(rewrite ETY; lia))
      as (Dy & HYd & HLY & Y0' & YC' & DY0 & DYC & SYR & SYA & ALY & UPY & _).
    set (br := getbn rr bs1) in *.
    set (la := firstn max (bn_buf (getbn x bs1))) in *. set (lb := firstn min (bn_buf (getbn y bs1))) in *.
    assert (LLA : length la = max) by (subst la; apply firstn_length_le; rewrite <- ETX; exact TDX).
    assert (LLB : length lb = min) by (subst lb; apply firstn_length_le; rewrite <- ETY; exact TDY).
    rewrite (usub_rest_eq rr x y bs1 max min HVR1 HTOPS) by (unfold bn_dmax in *; lia). fold br la lb.
    cbn [embed interp]. apply implM_interp_ret.
    assert (PREc : usub_pre sp lo R X Y Dr Dx Dy br la lb).
    { unfold usub_pre. rewrite LLA, LLB. specialize (DSEPR rr R HR1). fold br in DSEPR.
      split; [subst la; apply limbs_firstn; exact LMX|]. split; [subst lb; apply limbs_firstn; exact LMY|].
      split; [exact HTOPS|]. split; [exact OKR|]. split; [exact HDM|].
      split. { pose proof (proj2 (proj2 FROK)) as B63'. clear - SA0 SAC X0' XC' Y0' YC' DR0 DRC DX0 DXC DY0 DYC LO CEIL GLO SPR SPB B63' HDM LLA; unfold GLOBALS_TOP in *; repeat split; lia. }
      split; [clear - SXR; lia|]. split; [clear - SYR; lia|]. split; [exact DSEPR|]. split; [exact SXA|]. split; [exact SYA|].
      split; [exact ALX | exact ALY]. }
    replace (Z_to_bv 64 (Z.of_nat max - Z.of_nat min)) with (Z_to_bv 64 (Z.of_nat (length la) - Z.of_nat (length lb))) by (rewrite LLA, LLB; reflexivity).
    replace (Z_to_bv 64 (Z.of_nat max)) with (Z_to_bv 64 (Z.of_nat (length la))) by (rewrite LLA; reflexivity).
    replace (Z_to_bv 64 (Z.of_nat min)) with (Z_to_bv 64 (Z.of_nat (length lb))) by (rewrite LLB; reflexivity).
    eapply evt_mono.
    { eapply (usub_ucore ra sp gp (wz RATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc) with (lo := lo) (R := R) (A := X) (B := Y)
        (Dr := Dr) (Da := Dx) (Db := Dy) (br := br) (la := la) (lb := lb); [exact PREc | |].
      { unfold usub_upre. rewrite LLA, LLB.
        split; [apply hide_intro; exact (proj2 (ref_at_ualign st1 OW1 LB m2 bs1 PL EA rr R HEAP2 PARTS1 HR1 NRO))|].
        split; [unfold ub_ptr_ok; intros HMX; apply (bn_arr_ualign st1 OW1 LB m2 bs1 PL EA rr Dr br HEAP2 PARTS1 ARR); clear - HDM HMX; lia|].
        split; [exact UPX|]. split; [exact UPY|]. lia. }
      unfold core_mem. split; [exact SR|]. split; [exact UR|]. split; [exact HXd|]. split; [exact HYd|].
      split; [exact HLX|]. split; [exact HLY|]. split; [exact FR2|]. split; [exact ST2 | exact MI2]. }

    intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m3 & -> & MU & WM & MI3 & SR3 & UR3 & ST3).
    pose proof (usub_buf_len sp lo R X Y Dr Dx Dy br la lb PREc) as LU.
    pose proof (usub_bn_okm sp lo R X Y Dr Dx Dy br la lb PREc) as OKF.
    assert (OKF' : bg_ok (usub_bn br la lb)).
    { destruct OKF as (K1 & K2 & _ & K4). destruct OKR' as (_ & _ & K3 & _). split; [exact K1|]. split; [exact K2|]. split; [|exact K4].
      unfold bn_dmax, usub_bn in *. cbn [bn_buf] in *. rewrite LU. exact K3. }
    clear XC YC XC' YC' DXC DYC ALX ALY SXR SYR SXA SYA HXd HYd HLX HLY PREc.
    pose proof ARR as ARR'. unfold bn_arr in ARR'. destruct (bn_d br) as [pr|] eqn:Edr.
    2:{
      destruct (bn_arr_null PL rr m2 OW1 Dr br PWF1 (hpl_wref PL rr HP) Edr ARR) as [-> Eb].
      assert (ED0 : bn_dmax br = 0%nat) by (unfold bn_dmax; rewrite Eb; reflexivity).
      assert (EM0 : max = 0%nat) by (clear - HDM ED0; lia).
      rewrite LLA, EM0 in MU. change (8 * Z.of_nat 0) with 0 in MU. rewrite Z.add_0_r in MU.
      assert (MU' : munch [(R, R + 24); (bv_unsigned sp - 144, bv_unsigned sp)] m2 m3).
      { eapply munch_weaken; [|exact MU]. unfold sub_fp. cbn [outside]. intros a Ha. split; [lia | exact Ha]. }
      assert (HWL : Forall (w_lib bs1 OW1 PL lo (bv_unsigned sp)) [(R, R + 24); (bv_unsigned sp - 144, bv_unsigned sp)]).
      { constructor; [right; left; exists (qs, As, ns); cbn [blk_addr blk_size fst snd]; split; [exact Hins | lia]|].
        constructor; [left; cbn [fst snd]; lia | constructor]. }
      assert (WOK : Forall (w_ok OW1 LB bs1 PL EA (bv_unsigned sp) [rr]) [(R, R + 24); (bv_unsigned sp - 144, bv_unsigned sp)]).
      { constructor; [eapply (w_struct OW1 LB bs1 PL EA (bv_unsigned sp) false [rr] _ rr R); [left; reflexivity | exact HR1 | exact NRO | cbn; lia | cbn; lia]|].
        constructor; [apply w_stack; cbn; lia | constructor]. }
      unfold bn_post. exists t0', t1', t2', (Z_to_bv 64 1), a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m3, OW1, PL, errv2.
      split; [reflexivity|]. cbn [fst snd].
      split; [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP2 PARTS1 FROK MU' WM HWL CEIL)|].
      split.
      { unfold lib_state. eapply (lib_state_close [] bs1 m3 OW1 PL EA rr R); [| exact ND2 | exact HR1 | exact NRO | | exact OKF' |].
        - eapply (lib_state_frame st1 LB (bv_unsigned sp) B); [exact HEAP2 | exact LSH | exact MU' | exact WM | exact FROK | exact WOK].
        - exists 0. split; [exact SR3|]. apply (bn_arr_nil_intro PL rr m3 OW1 0 _ PWF1 (hpl_wref PL rr HP) eq_refl); [| cbn [usub_bn bn_d]; exact Edr].
          unfold usub_bn. cbn [bn_buf]. unfold usub_buf. rewrite LLA, EM0. cbn [Nat.eqb]. exact Eb.
        - apply ids_ok_setbn_same; [exact IDS1 | exact HVR1 |]. unfold bn_blocks, usub_bn. cbn [bn_d]. fold br. rewrite Edr. reflexivity. }
      split; [apply (seg_auxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP2 PARTS1 FROK AUX2 MU' WM HWL SPB ltac:(lia)); exact GLO'|].
      split; [exact ST3|].
      split. { eapply rw_cells_transport; [exact ERR2 | exact MU' | exact WM |]. unfold LX_ERRNO, RATP, GLOBALS_TOP in *. cbn. clear - SAI SA0 GLO LO SPR FBlo; lia. }
      split; [exact MI3|].
      split. { eapply lx_pres_trans; [exact LXP2|]. apply (seg_lx_pres _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP2 PARTS1 FROK MU' WM HWL CEIL); [exact GLO'| lia]. }
      split; [exact FA2|]. split; [exact SO2|].
      split. { eapply refs_stable_trans; [exact RS| apply refs_stable_setbn]. }
      unfold uarith_res. split; [reflexivity|]. split; [reflexivity | exact STAB]. }
    destruct ARR' as [HinR _].
    pose proof (RH_range _ _ _ _ _ _ _ HEAP2 HinR) as (_ & _ & _ & _ & DRI).
    rewrite LLA in MU.
    assert (HWL : Forall (w_lib bs1 OW1 PL lo (bv_unsigned sp)) [(Dr, Dr + 8 * Z.of_nat max); (R, R + 24); (bv_unsigned sp - 144, bv_unsigned sp)]).
    { constructor; [right; left; exists (pr, Dr, 8 * Z.of_nat (bn_dmax br)); cbn [blk_addr blk_size fst snd]; split; [exact HinR | lia]|].
      constructor; [right; left; exists (qs, As, ns); cbn [blk_addr blk_size fst snd]; split; [exact Hins | lia]|].
      constructor; [left; cbn [fst snd]; lia | constructor]. }
    assert (WOK : Forall (w_ok OW1 LB bs1 PL EA (bv_unsigned sp) [rr]) [(Dr, Dr + 8 * Z.of_nat max); (R, R + 24); (bv_unsigned sp - 144, bv_unsigned sp)]).
    { constructor; [eapply (w_limbs OW1 LB bs1 PL EA (bv_unsigned sp) false [rr] _ rr pr Dr); [left; reflexivity | exact HVR1 | exact Edr | exact HinR | cbn [fst snd]; lia | cbn [fst snd]; fold br; lia]|].
      constructor; [eapply (w_struct OW1 LB bs1 PL EA (bv_unsigned sp) false [rr] _ rr R); [left; reflexivity | exact HR1 | exact NRO | cbn; lia | cbn; lia]|].
      constructor; [apply w_stack; cbn; lia | constructor]. }
    unfold bn_post. exists t0', t1', t2', (Z_to_bv 64 1), a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m3, OW1, PL, errv2.
    split; [reflexivity|]. cbn [fst snd].
    split; [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP2 PARTS1 FROK MU WM HWL CEIL)|].
    split.
    { unfold lib_state. eapply (lib_state_close [] bs1 m3 OW1 PL EA rr R); [| exact ND2 | exact HR1 | exact NRO | | exact OKF' |].
      - eapply (lib_state_frame _ LB (bv_unsigned sp) B); [exact HEAP2| exact LSH| exact MU| exact WM| exact FROK| exact WOK].
      - exists Dr. split; [exact SR3|]. unfold bn_arr, usub_bn. cbn [bn_d]. rewrite Edr. unfold bn_dmax at 1. cbn [bn_buf]. rewrite LU.
        split; [exact HinR | exact UR3].
      - apply ids_ok_setbn_same; [exact IDS1 | exact HVR1 |]. unfold bn_blocks, usub_bn, bn_dmax. cbn [bn_d bn_buf]. rewrite LU. reflexivity. }
    split; [apply (seg_auxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP2 PARTS1 FROK AUX2 MU WM HWL SPB ltac:(lia)); exact GLO'|].
    split; [exact ST3|].
    split. { eapply rw_cells_transport; [exact ERR2 | exact MU | exact WM |]. unfold LX_ERRNO, RATP, GLOBALS_TOP in *. cbn. clear - DRI DR0 HDM LLA SAI SA0 GLO LO SPR FBlo; lia. }
    split; [exact MI3|].
    split. { eapply lx_pres_trans; [exact LXP2|]. apply (seg_lx_pres _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP2 PARTS1 FROK MU WM HWL CEIL); [exact GLO'| lia]. }
    split; [exact FA2|]. split; [exact SO2|].
    split. { eapply refs_stable_trans; [exact RS| apply refs_stable_setbn]. }
    unfold uarith_res. split; [reflexivity|]. split; [reflexivity | exact STAB].
  Qed.
End Proofs.
End WithCeiling0.
