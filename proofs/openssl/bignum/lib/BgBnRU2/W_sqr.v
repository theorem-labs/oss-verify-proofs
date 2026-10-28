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
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BnModel BnTree BnInv BnBridge BgState BgInv BgLib BgWords BgArith BgSqrCorrect.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Import Layout Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnArith BnMem BnTac BnTacX.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require Import BnHeap W_small W_top.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require BnRep BnLeaves BnAssoc.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgRepU Require Import BgRepDefs BgRep BgLayer BgIface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnRU Require Import BgLeaves BnRKit W_expand W_ctx W_ctx_get W_ctx_end.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnR Require Import BgLive DivModel.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnAU Require BnAKit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU2 Require W_ctx3.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnWU2 Require Import WU_sqr_words WU_sqr_normal SqrCalls HxSqr4 HxSqr8 WU_sqr_recursive.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnWU Require WU_num_bits_word.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnEU Require Import ExpKit.
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

Ltac to_implM :=
  lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
    lazymatch E with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.

Definition sqr_fin (b : bignum bptr) (max : nat) : bignum bptr := mkBN (bn_d b) (bn_buf b) max false (bn_flags b).

Lemma splice_full : forall (l seg : list Z), length seg = length l -> splice l 0 seg = seg.
Proof. intros l seg H. unfold splice. cbn [firstn app Nat.add]. rewrite H, skipn_all, app_nil_r. reflexivity. Qed.

Lemma sqr_model_fin : forall {ptr} rr (b : bignum ptr) max (bs : bstate ptr), (rr < length (st_bns bs))%nat ->
  setbn rr (mkBN (bn_d (getbn rr (setbn rr b bs))) (bn_buf (getbn rr (setbn rr b bs))) max false (bn_flags (getbn rr (setbn rr b bs)))) (setbn rr b bs)
  = setbn rr (mkBN (bn_d b) (bn_buf b) max false (bn_flags b)) bs.
Proof. intros ptr rr b max bs H. rewrite getbn_setbn_same by exact H. apply setbn_setbn_same. Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition BN_SQR_FIXED_TOP : Z := 0x1073bc.
Definition BN_SQR : Z := 0x107374.
Definition BN_SQR_FIXED_STACK : Z := 336 + BN_WEXPAND_STACK.
Definition BN_SQR_STACK : Z := 32 + BN_SQR_FIXED_STACK.

Definition sqr_frame (jb : list byte) (ra s0 s1 s2 s3 s4 s5 s6 s7 : word) : list cell :=
  [CB 264 jb; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition ub_kind (pc : Z) : Z :=
  match pc with
  | 1078248 => 2
  | 1078264 => 2
  | 1078340 => 2
  | 1078384 => 2
  | 1078404 => 2
  | 1078412 => 2
  | 1078436 => 2
  | 1078468 => 2
  | 1078500 => 2
  | 1078508 => 2
  | 1078528 => 2
  | 1078544 => 2
  | 1078572 => 2
  | 1078624 => 2
  | _ => 0
  end%Z.

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Lemma sqr_tail : forall
      (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs) (lo B : Z)
      (jb : list byte) (stx : PState) (bsx : bstate bptr) (mx : mem) (OWx : list block) (rr : bnref) (R ac : Z) (qc : bptr) (max : nat)
      (x1 t0 t1 t2 x8 a0 a1 a2 a3 a4 a5 a6 a7 x21 x22 x23 t3 t4 t5 t6 : word),
    kenv LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -336) s bs OW m (sqr_frame jb ra s0 s1 s2 s3 s4 s5 s6 s7) stx bsx mx OWx ->
    lib_state bsx mx OWx PL EA ->
    alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - BN_SQR_FIXED_STACK -> bv_unsigned sp <= B -> B < 2^63 -> frames_ok PL (bv_unsigned sp) B ->
    ref_at bsx OWx PL rr R -> hpl PL rr -> pl_ctx PL = Some (ac, qc) ->
    (max <= bn_dmax (getbn rr bsx))%nat ->
    implM bgusegs (interp (embed (BN_CTX_end (tree_ops bptr) (setbn rr (sqr_fin (getbn rr bsx) max) bsx)))) stx
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -336)) gp (wz RATP) t0 t1 t2 x8 (Z_to_bv 64 ac) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 R) (Z_to_bv 64 R) (Z_to_bv 64 (Z.of_nat max)) x21 x22 x23 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x107578) fc None mx (seg_rom bgusegs)).
  Proof.
    intros until t6. intros ENV LS CEIL GLO LO SPB B63 FROK HR HP HPC HMAX. pose proof (proj1 HP) as NRO.
    unfold BN_SQR_FIXED_STACK, BN_WEXPAND_STACK, BN_EXPAND2_STACK in LO. unfold sqr_frame in ENV.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (GLO' : GLOBALS_TOP <= lo) by exact GLO. unfold GLOBALS_TOP in GLO.
    assert (FBlo : lo <= bv_unsigned sp + -336) by lia.
    assert (FBsp : bv_unsigned sp + -336 <= bv_unsigned sp) by lia.
    assert (SPR2 : bv_unsigned sp < 2 ^ 64) by lia.
    pose proof (kenv_pre LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -336) s bs OW m CEIL GLO' FBlo FBsp SPB B63 SPR2 FROK) as KPRE.
    pose proof (kenv_post LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -336) s bs OW m CEIL GLO' FBlo FBsp FROK) as KPOST.
    pose proof (fun A => @bn_post_kpost _ _ LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -336) CEIL FBlo FBsp SPR2 A) as BPK.
    pose proof ENV as (HEAP & AUX & ST & (errv & ERR) & MI & LXP & FA & SO & RS & FR & FSZ).
    unfold LX_ERRNO, RATP in ERR. change (3346328 - 164) with 3346164 in ERR.
    pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
    destruct (lib_state_open [] bsx mx OWx PL EA rr R LS ND HR ltac:(intros []) NRO) as ((Dr & SR & ARR) & OKR & LSH).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HR) as HVR.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS; pose proof PARTS as (WFS & PWF & IDS & PLB & ERRB).
    destruct (bn_arr_facts_w bsx OWx PL EA (bv_unsigned sp) B stx LB mx rr Dr HEAP PARTS FROK HVR (hpl_wref PL rr HP) ARR) as (U & LENW & D0 & DC & DI & DSEP).
    specialize (DSEP rr R HR).
    pose proof (ref_at_hrange _ _ _ _ _ _ _ _ _ HEAP PARTS HR HP) as (SA0 & SAC & SAI & (qs & As & ns & Hins & Ra1 & Ra2)).
    set (b := getbn rr bsx) in *.
    unfold bn_cells, MallocRep.wz in SR.
    pose proof (munch_refl [(R, R + 24)]%Z mx) as MU. pose proof (wmono_refl bgusegs mx) as WM.
    assert (DMB : Z.of_nat (bn_dmax b) <= 512) by (destruct OKR as (_ & _ & O3 & _); unfold BG_DMAX in O3; exact O3).
    unfold implM. iprefix.
    step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) => rename mf into m1 end.
    assert (HWL : Forall (w_lib bsx OWx PL lo (bv_unsigned sp)) [(R, R + 24)]).
    { constructor; [right; left; exists (qs, As, ns); cbn [blk_addr blk_size fst snd]; split; [exact Hins | lia] | constructor]. }
    assert (WOK : Forall (w_ok OWx LB bsx PL EA (bv_unsigned sp) [rr]) [(R, R + 24)]).
    { constructor; [eapply (w_struct OWx LB bsx PL EA (bv_unsigned sp) false [rr] _ rr R); [left; reflexivity | exact HR | exact NRO | cbn; lia | cbn; lia] | constructor]. }
    assert (LS1 : lib_state (setbn rr (sqr_fin b max) bsx) m1 OWx PL EA).
    { unfold lib_state. eapply (lib_state_close [] bsx m1 OWx PL EA rr R); [| exact ND | exact HR | exact NRO | | |].
      - eapply (lib_state_frame stx LB (bv_unsigned sp) B); [exact HEAP| exact LSH| exact MU| exact WM| exact FROK| exact WOK].
      - exists Dr. split; [unfold bn_cells, sqr_fin, bn_dmax; cbn [bn_top bn_buf bn_neg bn_flags Z.b2z]; exact SR|].
        eapply bn_arr_of_u64arr; [exact ARR | exact U].
      - destruct OKR as (O1 & O2 & O3 & O4). unfold bg_ok, sqr_fin, bn_dmax in *. cbn [bn_top bn_buf bn_flags]. auto.
      - apply ids_ok_setbn_same; [exact IDS | exact HVR | reflexivity]. }
    assert (ENV1 : kenv LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -336) s bs OW m
                     [CB 264 jb; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] stx (setbn rr (sqr_fin b max) bsx) m1 OWx).
    { apply kenv_setbn.
      eapply (kenv_silent LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -336) s bs OW m CEIL GLO' FBlo FBsp SPB FROK) with (errv' := errv);
        [exact ENV | exact PARTS | exact MU | exact WM | exact HWL | exact ST | unfold LX_ERRNO, RATP; exact ERR | exact MI | exact FR | exact FSZ]. }
    clear ENV LS LSH SR U ARR ST ERR MI FR MU WM HWL WOK HEAP AUX LXP FA SO RS.

    step. if_true.
    step. step. step.
    destruct (KPRE _ _ _ _ _ BN_CTX_END_STACK ENV1 LS1 ltac:(unfold BN_CTX_END_STACK; lia)) as (errv1 & PRE1).
    step.
    ihere. to_implM.
    eapply implM_post_evt.
    { eapply BN_CTX_end_walk; [exact PRE1| reflexivity| exact HPC| reflexivity]. }
    cbv beta. intros [u6 bs6] st6 ms6 PO. apply BPK in PO; [|intros v b0 o p a [E _]; exact E].
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m6 & OW6 & -> & KP & (_ & EOW6)).
    destruct (KPOST _ _ _ _ _ _ _ _ _ ENV1 KP) as (ENV6 & LS6).
    cbn [fst snd] in *. clear PRE1 KP.
    replace (ret_pc (Z_to_bv 64 1078696)) with (Z_to_bv 64 1078696) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (kenv_final LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -336) s bs OW m _ _ _ _ _ ENV6) as (F1 & F2 & STF & (errvF & F4) & F5 & F6 & F7 & F8 & F9 & FRF).
    step. do 9 step. release_frame FRF STF (bv_unsigned sp). step. step.
    apply evt_done. unfold bn_post. do 15 eexists. exists m6, OW6, PL, errvF. split; [reflexivity|]. cbn [fst snd].
    split; [exact F1|]. split; [exact LS6|]. split; [exact F2|]. split; [exact STF|]. split; [exact F4|]. split; [exact F5|].
    split; [exact F6|]. split; [exact F7|]. split; [exact F8|]. split; [exact F9|]. split; reflexivity.
  Qed.

  Lemma sqr_finish2 : forall
      (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs) (lo B : Z)
      (jb jb' : list byte) (st3 : PState) (bs3 : bstate bptr) (m3 m4 : mem) (OW3 : list block) (rr t : bnref) (R TT ac Dr Dt CST : Z) (qc : bptr) (max : nat)
      (w tw : list Z)
      (x1 t0 t1 t2 x8 a0 a1 a2 a3 a4 a5 a6 a7 x21 x22 x23 t3 t4 t5 t6 : word),
    kenv LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -336) s bs OW m (sqr_frame jb ra s0 s1 s2 s3 s4 s5 s6 s7) st3 bs3 m3 OW3 ->
    lib_state bs3 m3 OW3 PL EA ->
    alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - BN_SQR_FIXED_STACK -> bv_unsigned sp <= B -> B < 2^63 -> frames_ok PL (bv_unsigned sp) B ->
    ref_at bs3 OW3 PL rr R -> hpl PL rr -> ref_at bs3 OW3 PL t TT -> hpl PL t -> t <> rr -> pl_ctx PL = Some (ac, qc) ->
    rw_cells bgusegs m3 R (bn_cells Dr (getbn rr bs3)) -> bn_arr m3 OW3 (pl_of PL rr) Dr (getbn rr bs3) ->
    rw_cells bgusegs m3 TT (bn_cells Dt (getbn t bs3)) -> bn_arr m3 OW3 (pl_of PL t) Dt (getbn t bs3) ->
    limbs w -> length w = max -> (0 < max <= bn_dmax (getbn rr bs3))%nat ->
    limbs tw -> (0 < length tw <= bn_dmax (getbn t bs3))%nat ->
    0 <= CST -> lo <= bv_unsigned sp - 336 - CST ->
    munch [(Dr, Dr + 8 * Z.of_nat max); (Dt, Dt + 8 * Z.of_nat (length tw)); (bv_unsigned sp - 336 - CST, bv_unsigned sp + -72)] m3 m4 ->
    wmono bgusegs m3 m4 -> mem_inv bgusegs m4 -> stk bgusegs m4 lo (bv_unsigned sp + -336) ->
    limbs_at bgusegs m4 Dr w -> limbs_at bgusegs m4 Dt tw ->
    rw_cells bgusegs m4 (bv_unsigned sp + -336) (sqr_frame jb' ra s0 s1 s2 s3 s4 s5 s6 s7) ->
    implM bgusegs (interp (embed (BN_CTX_end (tree_ops bptr)
              (setbn rr (sqr_fin (bn_with_buf (getbn rr bs3) (splice (bn_buf (getbn rr bs3)) 0 w)) max)
                 (setbn t (bn_with_buf (getbn t bs3) (splice (bn_buf (getbn t bs3)) 0 tw)) bs3))))) st3
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -336)) gp (wz RATP) t0 t1 t2 x8 (Z_to_bv 64 ac) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 R) (Z_to_bv 64 R) (Z_to_bv 64 (Z.of_nat max)) x21 x22 x23 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x107578) fc None m4 (seg_rom bgusegs)).
  Proof.
    intros until t6. intros ENV LS CEIL GLO LO SPB B63 FROK HR HP HT HPT NTR HPC SR ARR STT ARRT LW ELW [HW0 HWD] LTW [HT0 HTD] HCST LOC MU WM MI4 ST4 HR4 HT4 FR4.
    pose proof (proj1 HP) as NRO. pose proof (proj1 HPT) as NROT.
    pose proof LO as LO'. unfold BN_SQR_FIXED_STACK, BN_WEXPAND_STACK, BN_EXPAND2_STACK in LO'.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (GLO' : GLOBALS_TOP <= lo) by exact GLO. unfold GLOBALS_TOP in GLO.
    assert (FBlo : lo <= bv_unsigned sp + -336) by lia.
    assert (FBsp : bv_unsigned sp + -336 <= bv_unsigned sp) by lia.
    pose proof ENV as (HEAP & AUX & ST & (errv & ERR) & MI & LXP & FA & SO & RS & FR & FSZ).
    unfold LX_ERRNO, RATP in ERR. change (3346328 - 164) with 3346164 in ERR.
    pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
    destruct (lib_state_open [] bs3 m3 OW3 PL EA rr R LS ND HR ltac:(intros []) NRO) as (_ & OKR & LSH1).
    destruct (lib_state_open [rr] bs3 m3 OW3 PL EA t TT LSH1 ND HT ltac:(intros [E|[]]; apply NTR; symmetry; exact E) NROT) as (_ & OKT & LSH2).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HR) as HVR. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HT) as HVT.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS; pose proof PARTS as (WFS & PWF & IDS & PLB & ERRB).
    destruct (bn_arr_facts_w bs3 OW3 PL EA (bv_unsigned sp) B st3 LB m3 rr Dr HEAP PARTS FROK HVR (hpl_wref PL rr HP) ARR) as (U & _ & D0 & DC & DRI & DSEP).
    destruct (bn_arr_facts_w bs3 OW3 PL EA (bv_unsigned sp) B st3 LB m3 t Dt HEAP PARTS FROK HVT (hpl_wref PL t HPT) ARRT) as (UT & _ & DT0 & DTC & DTI & DSEPT).
    pose proof (DSEP rr R HR) as DSR. pose proof (DSEP t TT HT) as DSRT. pose proof (DSEPT rr R HR) as DSTR. pose proof (DSEPT t TT HT) as DSTT.
    pose proof (bn_arrs_disj st3 OW3 LB m3 bs3 PL EA (bv_unsigned sp) B rr t R TT Dr Dt HEAP LS FROK ltac:(congruence) HR HT NRO NROT ARR ARRT) as ADJ.
    pose proof (ref_at_hrange _ _ _ _ _ _ _ _ _ HEAP PARTS HR HP) as (SA0 & SAC & SAI & (qs & As & ns & Hins & Ra1 & Ra2)).
    pose proof (ref_at_hrange _ _ _ _ _ _ _ _ _ HEAP PARTS HT HPT) as (TA0 & TAC & TAI & (qt & At & nt & Hint & Rt1 & Rt2)).
    set (br := getbn rr bs3) in *. set (tb := getbn t bs3) in *.
    assert (LBR : length (bn_buf br) = bn_dmax br) by reflexivity. assert (LBT : length (bn_buf tb) = bn_dmax tb) by reflexivity.
    unfold bn_arr in ARR. destruct (bn_d br) as [pr|] eqn:Edr.
    2:{ exfalso. destruct (bn_arr_null PL rr m3 OW3 Dr br PWF (hpl_wref PL rr HP) Edr ltac:(unfold bn_arr; rewrite Edr; exact ARR)) as [_ Eb]. rewrite Eb in LBR. cbn [length] in LBR. lia. }
    destruct ARR as [HinR _].
    unfold bn_arr in ARRT. destruct (bn_d tb) as [pt|] eqn:Edt.
    2:{ exfalso. destruct (bn_arr_null PL t m3 OW3 Dt tb PWF (hpl_wref PL t HPT) Edt ltac:(unfold bn_arr; rewrite Edt; exact ARRT)) as [_ Eb]. rewrite Eb in LBT. cbn [length] in LBT. lia. }
    destruct ARRT as [HinT _].
    set (W := [(Dr, Dr + 8 * Z.of_nat max); (Dt, Dt + 8 * Z.of_nat (length tw)); (bv_unsigned sp - 336 - CST, bv_unsigned sp + -72)]) in *.
    assert (HWL : Forall (w_lib bs3 OW3 PL lo (bv_unsigned sp)) W).
    { constructor; [right; left; exists (pr, Dr, 8 * Z.of_nat (bn_dmax br)); cbn [blk_addr blk_size fst snd]; split; [exact HinR | clear - HWD; lia]|].
      constructor; [right; left; exists (pt, Dt, 8 * Z.of_nat (bn_dmax tb)); cbn [blk_addr blk_size fst snd]; split; [exact HinT | clear - HTD; lia]|].
      constructor; [left; cbn [fst snd]; clear - LOC HCST; lia | constructor]. }
    assert (WOK : Forall (w_ok OW3 LB bs3 PL EA (bv_unsigned sp) [t; rr]) W).
    { constructor; [eapply (w_limbs OW3 LB bs3 PL EA (bv_unsigned sp) false [t; rr] _ rr pr Dr); [right; left; reflexivity | exact HVR | exact Edr | exact HinR | cbn [fst snd]; clear; lia | cbn [fst snd]; fold br; clear - HWD; lia]|].
      constructor; [eapply (w_limbs OW3 LB bs3 PL EA (bv_unsigned sp) false [t; rr] _ t pt Dt); [left; reflexivity | exact HVT | exact Edt | exact HinT | cbn [fst snd]; clear; lia | cbn [fst snd]; fold tb; clear - HTD; lia]|].
      constructor; [apply w_stack; cbn [fst snd]; clear - LOC HCST CEIL; lia | constructor]. }
    pose proof (lib_state_frame st3 LB (bv_unsigned sp) B [t; rr] bs3 m3 m4 OW3 PL EA _ HEAP LSH2 MU WM FROK WOK) as LSH2'.
    assert (SR4 : rw_cells bgusegs m4 R (bn_cells Dr br)).
    { eapply rw_cells_transport; [exact SR | exact MU | exact WM |]. subst W. cbn. clear - DSR DSTR SAC CEIL LOC HCST HWD HTD. lia. }
    assert (ST4' : rw_cells bgusegs m4 TT (bn_cells Dt tb)).
    { eapply rw_cells_transport; [exact STT | exact MU | exact WM |]. subst W. cbn. clear - DSRT DSTT TAC CEIL LOC HCST HWD HTD. lia. }
    assert (ERR4 : rw_cells bgusegs m4 3346164 [C4 errv]).
    { eapply rw_cells_transport; [exact ERR | exact MU | exact WM |]. subst W. cbn. clear - DRI DTI D0 DT0 GLO LOC HCST HWD HTD HW0 HT0. lia. }

    set (tb' := bn_with_buf tb (splice (bn_buf tb) 0 tw)).
    assert (LSPT : length (splice (bn_buf tb) 0 tw) = bn_dmax tb) by (rewrite splice_length; [exact LBT| rewrite LBT; clear - HTD; lia]).
    assert (LSH1' : lib_state_h [rr] (setbn t tb' bs3) m4 OW3 PL EA).
    { eapply (lib_state_close [rr] bs3 m4 OW3 PL EA t TT); [exact LSH2' | exact ND | exact HT | exact NROT | | |].
      - exists Dt. split.
        + unfold tb', bn_cells, bn_with_buf, bn_dmax. cbn [bn_top bn_buf bn_neg bn_flags]. rewrite LSPT. exact ST4'.
        + unfold bn_arr, tb', bn_with_buf, bn_dmax. cbn [bn_d bn_buf]. rewrite Edt, LSPT.
          split; [exact HinT|].
          eapply BnAKit.arr_splice0; [exact UT | exact MU | exact WM | exact HT4 | rewrite LBT; clear - HTD; lia | |]; subst W; cbn [disjoint_from]; rewrite ?LBT; clear - ADJ DTC CEIL LOC HCST HWD HTD; lia.
      - destruct OKT as (O1 & O2 & O3 & O4). unfold bg_ok, tb', bn_with_buf, bn_dmax in *. cbn [bn_top bn_buf bn_flags]. rewrite LSPT.
        split; [apply splice_limbs; [exact O1| exact LTW]|]. auto.
      - apply ids_ok_setbn_same; [exact IDS | exact HVT |]. unfold bn_blocks, tb', bn_with_buf, bn_dmax. cbn [bn_d bn_buf]. rewrite LSPT. reflexivity. }

    set (bs3' := setbn t tb' bs3) in *.
    set (br' := bn_with_buf br (splice (bn_buf br) 0 w)).
    assert (LSP : length (splice (bn_buf br) 0 w) = bn_dmax br) by (rewrite splice_length; [exact LBR| rewrite LBR, ELW; clear - HWD; lia]).
    assert (EGR : getbn rr bs3' = br) by (unfold bs3'; apply getbn_setbn_other; exact NTR).
    assert (HR' : ref_at bs3' OW3 PL rr R) by (apply ref_at_setbn; exact HR).
    assert (HVR' : vref rr bs3') by (unfold bs3', vref; rewrite length_setbn; exact HVR).
    pose proof (lib_state_h_parts _ _ _ _ _ _ LSH1') as PARTS'. pose proof PARTS' as (_ & _ & IDS' & _).
    assert (LSN : lib_state (setbn rr br' bs3') m4 OW3 PL EA).
    { unfold lib_state. eapply (lib_state_close [] bs3' m4 OW3 PL EA rr R); [exact LSH1' | exact ND | exact HR' | exact NRO | | |].
      - exists Dr. split; [unfold br', bn_cells, bn_with_buf, bn_dmax; cbn [bn_top bn_buf bn_neg bn_flags]; rewrite LSP; exact SR4|].
        unfold bn_arr, br', bn_with_buf, bn_dmax. cbn [bn_d bn_buf]. rewrite Edr, LSP.
        split; [exact HinR|].
        eapply BnAKit.arr_splice0; [exact U | exact MU | exact WM | exact HR4 | rewrite LBR, ELW; clear - HWD; lia | |]; subst W; cbn [disjoint_from]; rewrite ?LBR, ?ELW; clear - ADJ DC CEIL LOC HCST HWD HTD; lia.
      - destruct OKR as (O1 & O2 & O3 & O4). unfold bg_ok, br', bn_with_buf, bn_dmax in *. cbn [bn_top bn_buf bn_flags]. rewrite LSP.
        split; [apply splice_limbs; [exact O1| exact LW]|]. auto.
      - apply ids_ok_setbn_same; [exact IDS' | exact HVR' |]. rewrite EGR. unfold bn_blocks, br', bn_with_buf, bn_dmax. cbn [bn_d bn_buf]. rewrite LSP. reflexivity. }
    assert (ENVN : kenv LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -336) s bs OW m (sqr_frame jb' ra s0 s1 s2 s3 s4 s5 s6 s7) st3 (setbn rr br' bs3') m4 OW3).
    { apply kenv_setbn. apply kenv_setbn.
      eapply (kenv_silent LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -336) s bs OW m CEIL GLO' FBlo FBsp SPB FROK) with (errv' := errv);
        [exact ENV | exact PARTS | exact MU | exact WM | exact HWL | exact ST4 | unfold LX_ERRNO, RATP; exact ERR4 | exact MI4 | exact FR4 | cbn; clear; lia]. }

    replace (setbn rr (sqr_fin br' max) bs3') with (setbn rr (sqr_fin (getbn rr (setbn rr br' bs3')) max) (setbn rr br' bs3'))
      by (rewrite getbn_setbn_same by exact HVR'; apply setbn_setbn_same).
    eapply sqr_tail; [exact ENVN | exact LSN | exact CEIL | exact GLO' | exact LO | exact SPB | exact B63 | exact FROK
      | apply ref_at_setbn; exact HR' | exact HP | exact HPC |].
    rewrite getbn_setbn_same by exact HVR'. unfold br', bn_with_buf, bn_dmax. cbn [bn_buf]. rewrite LSP. exact (proj2 (conj HW0 HWD)).
  Qed.

  Lemma sqr_finish1 : forall
      (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs) (lo B : Z)
      (jb jb' : list byte) (st3 : PState) (bs3 : bstate bptr) (m3 m4 : mem) (OW3 : list block) (rr : bnref) (R ac Dr CST : Z) (qc : bptr) (max : nat)
      (w : list Z)
      (x1 t0 t1 t2 x8 a0 a1 a2 a3 a4 a5 a6 a7 x21 x22 x23 t3 t4 t5 t6 : word),
    kenv LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -336) s bs OW m (sqr_frame jb ra s0 s1 s2 s3 s4 s5 s6 s7) st3 bs3 m3 OW3 ->
    lib_state bs3 m3 OW3 PL EA ->
    alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - BN_SQR_FIXED_STACK -> bv_unsigned sp <= B -> B < 2^63 -> frames_ok PL (bv_unsigned sp) B ->
    ref_at bs3 OW3 PL rr R -> hpl PL rr -> pl_ctx PL = Some (ac, qc) ->
    rw_cells bgusegs m3 R (bn_cells Dr (getbn rr bs3)) -> bn_arr m3 OW3 (pl_of PL rr) Dr (getbn rr bs3) ->
    limbs w -> length w = max -> (0 < max <= bn_dmax (getbn rr bs3))%nat ->
    0 <= CST -> lo <= bv_unsigned sp - 336 - CST ->
    munch [(Dr, Dr + 8 * Z.of_nat max); (bv_unsigned sp - 336 - CST, bv_unsigned sp + -72)] m3 m4 ->
    wmono bgusegs m3 m4 -> mem_inv bgusegs m4 -> stk bgusegs m4 lo (bv_unsigned sp + -336) ->
    limbs_at bgusegs m4 Dr w ->
    rw_cells bgusegs m4 (bv_unsigned sp + -336) (sqr_frame jb' ra s0 s1 s2 s3 s4 s5 s6 s7) ->
    implM bgusegs (interp (embed (BN_CTX_end (tree_ops bptr)
              (setbn rr (sqr_fin (bn_with_buf (getbn rr bs3) (splice (bn_buf (getbn rr bs3)) 0 w)) max) bs3)))) st3
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -336)) gp (wz RATP) t0 t1 t2 x8 (Z_to_bv 64 ac) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 R) (Z_to_bv 64 R) (Z_to_bv 64 (Z.of_nat max)) x21 x22 x23 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x107578) fc None m4 (seg_rom bgusegs)).
  Proof.
    intros until t6. intros ENV LS CEIL GLO LO SPB B63 FROK HR HP HPC SR ARR LW ELW [HW0 HWD] HCST LOC MU WM MI4 ST4 HR4 FR4.
    pose proof (proj1 HP) as NRO.
    pose proof LO as LO'. unfold BN_SQR_FIXED_STACK, BN_WEXPAND_STACK, BN_EXPAND2_STACK in LO'.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (GLO' : GLOBALS_TOP <= lo) by exact GLO. unfold GLOBALS_TOP in GLO.
    assert (FBlo : lo <= bv_unsigned sp + -336) by lia.
    assert (FBsp : bv_unsigned sp + -336 <= bv_unsigned sp) by lia.
    pose proof ENV as (HEAP & AUX & ST & (errv & ERR) & MI & LXP & FA & SO & RS & FR & FSZ).
    unfold LX_ERRNO, RATP in ERR. change (3346328 - 164) with 3346164 in ERR.
    pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
    destruct (lib_state_open [] bs3 m3 OW3 PL EA rr R LS ND HR ltac:(intros []) NRO) as (_ & OKR & LSH1).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HR) as HVR.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS; pose proof PARTS as (WFS & PWF & IDS & PLB & ERRB).
    destruct (bn_arr_facts_w bs3 OW3 PL EA (bv_unsigned sp) B st3 LB m3 rr Dr HEAP PARTS FROK HVR (hpl_wref PL rr HP) ARR) as (U & _ & D0 & DC & DRI & DSEP).
    pose proof (DSEP rr R HR) as DSR.
    pose proof (ref_at_hrange _ _ _ _ _ _ _ _ _ HEAP PARTS HR HP) as (SA0 & SAC & SAI & (qs & As & ns & Hins & Ra1 & Ra2)).
    set (br := getbn rr bs3) in *.
    assert (LBR : length (bn_buf br) = bn_dmax br) by reflexivity.
    unfold bn_arr in ARR. destruct (bn_d br) as [pr|] eqn:Edr.
    2:{ exfalso. destruct (bn_arr_null PL rr m3 OW3 Dr br PWF (hpl_wref PL rr HP) Edr ltac:(unfold bn_arr; rewrite Edr; exact ARR)) as [_ Eb]. rewrite Eb in LBR. cbn [length] in LBR. lia. }
    destruct ARR as [HinR _].
    set (W := [(Dr, Dr + 8 * Z.of_nat max); (bv_unsigned sp - 336 - CST, bv_unsigned sp + -72)]) in *.
    assert (HWL : Forall (w_lib bs3 OW3 PL lo (bv_unsigned sp)) W).
    { constructor; [right; left; exists (pr, Dr, 8 * Z.of_nat (bn_dmax br)); cbn [blk_addr blk_size fst snd]; split; [exact HinR | clear - HWD; lia]|].
      constructor; [left; cbn [fst snd]; clear - LOC HCST; lia | constructor]. }
    assert (WOK : Forall (w_ok OW3 LB bs3 PL EA (bv_unsigned sp) [rr]) W).
    { constructor; [eapply (w_limbs OW3 LB bs3 PL EA (bv_unsigned sp) false [rr] _ rr pr Dr); [left; reflexivity | exact HVR | exact Edr | exact HinR | cbn [fst snd]; clear; lia | cbn [fst snd]; fold br; clear - HWD; lia]|].
      constructor; [apply w_stack; cbn [fst snd]; clear - LOC HCST CEIL; lia | constructor]. }
    pose proof (lib_state_frame st3 LB (bv_unsigned sp) B [rr] bs3 m3 m4 OW3 PL EA _ HEAP LSH1 MU WM FROK WOK) as LSH1'.
    assert (SR4 : rw_cells bgusegs m4 R (bn_cells Dr br)).
    { eapply rw_cells_transport; [exact SR | exact MU | exact WM |]. subst W. cbn. clear - DSR SAC CEIL LOC HCST HWD. lia. }
    assert (ERR4 : rw_cells bgusegs m4 3346164 [C4 errv]).
    { eapply rw_cells_transport; [exact ERR | exact MU | exact WM |]. subst W. cbn. clear - DRI D0 GLO LOC HCST HWD HW0. lia. }
    set (br' := bn_with_buf br (splice (bn_buf br) 0 w)).
    assert (LSP : length (splice (bn_buf br) 0 w) = bn_dmax br) by (rewrite splice_length; [exact LBR| rewrite LBR, ELW; clear - HWD; lia]).
    assert (LSN : lib_state (setbn rr br' bs3) m4 OW3 PL EA).
    { unfold lib_state. eapply (lib_state_close [] bs3 m4 OW3 PL EA rr R); [exact LSH1' | exact ND | exact HR | exact NRO | | |].
      - exists Dr. split; [unfold br', bn_cells, bn_with_buf, bn_dmax; cbn [bn_top bn_buf bn_neg bn_flags]; rewrite LSP; exact SR4|].
        unfold bn_arr, br', bn_with_buf, bn_dmax. cbn [bn_d bn_buf]. rewrite Edr, LSP.
        split; [exact HinR|].
        eapply BnAKit.arr_splice0; [exact U | exact MU | exact WM | exact HR4 | rewrite LBR, ELW; clear - HWD; lia | |]; subst W; cbn [disjoint_from]; rewrite ?LBR, ?ELW; clear - DC CEIL LOC HCST HWD; lia.
      - destruct OKR as (O1 & O2 & O3 & O4). unfold bg_ok, br', bn_with_buf, bn_dmax in *. cbn [bn_top bn_buf bn_flags]. rewrite LSP.
        split; [apply splice_limbs; [exact O1| exact LW]|]. auto.
      - apply ids_ok_setbn_same; [exact IDS | exact HVR |]. unfold bn_blocks, br', bn_with_buf, bn_dmax. cbn [bn_d bn_buf]. rewrite LSP. reflexivity. }
    assert (ENVN : kenv LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -336) s bs OW m (sqr_frame jb' ra s0 s1 s2 s3 s4 s5 s6 s7) st3 (setbn rr br' bs3) m4 OW3).
    { apply kenv_setbn.
      eapply (kenv_silent LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -336) s bs OW m CEIL GLO' FBlo FBsp SPB FROK) with (errv' := errv);
        [exact ENV | exact PARTS | exact MU | exact WM | exact HWL | exact ST4 | unfold LX_ERRNO, RATP; exact ERR4 | exact MI4 | exact FR4 | cbn; clear; lia]. }
    replace (setbn rr (sqr_fin br' max) bs3) with (setbn rr (sqr_fin (getbn rr (setbn rr br' bs3)) max) (setbn rr br' bs3))
      by (rewrite getbn_setbn_same by exact HVR; apply setbn_setbn_same).
    eapply sqr_tail; [exact ENVN | exact LSN | exact CEIL | exact GLO' | exact LO | exact SPB | exact B63 | exact FROK
      | apply ref_at_setbn; exact HR | exact HP | exact HPC |].
    rewrite getbn_setbn_same by exact HVR. unfold br', bn_with_buf, bn_dmax. cbn [bn_buf]. rewrite LSP. exact HWD.
  Qed.

  Lemma sqr_path_comba4 : forall
      (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs) (lo B : Z)
      (jb : list byte) (st3 : PState) (bs3 : bstate bptr) (m3 : mem) (OW3 : list block) (rr rx : bnref) (R A ac : Z) (qc : bptr)
      (x1 t0 t1 t2 x8 a0 a1 a2 a3 a4 a5 a6 a7 x22 x23 t3 t4 t5 t6 : word),
    kenv LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -336) s bs OW m (sqr_frame jb ra s0 s1 s2 s3 s4 s5 s6 s7) st3 bs3 m3 OW3 ->
    lib_state bs3 m3 OW3 PL EA ->
    alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - BN_SQR_FIXED_STACK -> bv_unsigned sp <= B -> B < 2^63 -> frames_ok PL (bv_unsigned sp) B ->
    ref_at bs3 OW3 PL rr R -> hpl PL rr -> ref_at bs3 OW3 PL rx A -> rx <> ROne -> rx <> rr -> pl_ctx PL = Some (ac, qc) ->
    (4 <= bn_top (getbn rx bs3))%nat -> (8 <= bn_dmax (getbn rr bs3))%nat ->
    implM bgusegs (interp (embed (BN_CTX_end (tree_ops bptr)
              (setbn rr (sqr_fin (bn_with_buf (getbn rr bs3) (splice (bn_buf (getbn rr bs3)) 0 (sqr_comba4 (firstn 4 (bn_buf (getbn rx bs3)))))) 8) bs3)))) st3
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -336)) gp (wz RATP) t0 t1 t2 x8 (Z_to_bv 64 ac) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 R) (Z_to_bv 64 R) (Z_to_bv 64 (Z.of_nat 8)) (Z_to_bv 64 A) x22 x23 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x10746c) fc None m3 (seg_rom bgusegs)).
  Proof.
    intros until t6. intros ENV LS CEIL GLO LO SPB B63 FROK HR HP HX NX NXR HPC HAL HDM.
    pose proof LO as LO'. unfold BN_SQR_FIXED_STACK, BN_WEXPAND_STACK, BN_EXPAND2_STACK in LO'.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof ENV as (HEAP & _ & ST & _ & MI & _ & _ & _ & _ & FR & _). unfold sqr_frame in FR.
    destruct (open_full st3 OW3 LB m3 bs3 PL EA (bv_unsigned sp) B rr R HEAP LS FROK HR HP) as (Dr & SR & ARR & OKR & UR & R0 & RC & DR0 & DRC & DSEP).
    destruct (operand_view_ne st3 OW3 LB m3 bs3 PL EA (bv_unsigned sp) B rr R Dr rx A 4 HEAP LS FROK HR HP SR ARR HX NX HAL NXR)
      as (Dx & SX & LX & UX & ARX & X0 & XC & DX0 & DXC & XR & RDX & XDR & DRX).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HX) as HVX. pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS. pose proof PARTS as (WFS & _).
    pose proof (st_wf_ok rx bs3 WFS HVX NX) as (LMX & TDX & DMX & _). unfold BG_DMAX in DMX.
    pose proof (ref_at_ualign _ _ _ _ _ _ _ _ _ HEAP PARTS HR (proj1 HP)) as (_ & RAL).
    pose proof (bn_arr_ualign _ _ _ _ _ _ _ _ _ _ HEAP PARTS ARR ltac:(clear - HDM; lia)) as DRAL.
    pose proof (bn_arr_ualign _ _ _ _ _ _ _ _ _ _ HEAP PARTS ARX ltac:(clear - TDX HAL; unfold bn_dmax in *; lia)) as DXAL.
    set (br := getbn rr bs3) in *. set (bx := getbn rx bs3) in *. set (la := firstn 4 (bn_buf bx)) in *.
    assert (LLA : length la = 4%nat) by (unfold la; rewrite firstn_length_le; [reflexivity| unfold bn_dmax in TDX; lia]).
    assert (LIA : limbs la) by (apply limbs_firstn; exact LMX).
    pose proof (proj1 (limbarr_limbs_at bgusegs m3 Dr (bn_buf br)) UR) as [_ HW]. fold (bn_dmax br) in HW.
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -336)) = bv_unsigned sp + -336) by (apply unsigned_lit; lia).
    assert (EDr : bv_unsigned (Z_to_bv 64 Dr) = Dr) by (apply unsigned_lit; lia).
    assert (EDx : bv_unsigned (Z_to_bv 64 Dx) = Dx) by (apply unsigned_lit; clear - DX0 DXC CEIL LO' SPR; lia).
    pose proof SR as SR'. unfold bn_cells, MallocRep.wz in SR'. unfold MallocRep.wz in SX.
    unfold implM. iprefix.
    step. ub1 ub_kind.
    step. step. clear SR' SX.
    step.
    eapply evt_cut.
    { eapply sqr_comba4_ok with (a := la) (lo := lo) (m := m3); rewrite ?EDr, ?EDx, ?ESP; unfold HxSqr4.CSQ;
        [ exact LIA | exact LLA | exact LX | replace Dr with (Dr + 0) by lia; eapply wr_at_sub; [exact HW| | |]; clear - HDM; lia
        | clear - DRX HDM TDX HAL; unfold bn_dmax in *; lia | exact ST | clear - LO'; lia | clear - DRC CEIL LO'; lia | clear - DXC CEIL LO' TDX; unfold bn_dmax in *; lia | exact MI
        | intros _; exact DRAL | intros _; exact DXAL ]. }
    intros ms' PO. unfold W_mul_normal.vl_post in PO.
    destruct PO as (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m4 & E & MUc & WMc & MIc & RES & STc).
    subst ms'. rewrite ?EDr, ?ESP in *. unfold HxSqr4.CSQ in MUc.
    lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?r)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 r)) with (Z_to_bv 64 r) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.
    eapply (rw_cells_transport bgusegs _ m3 m4) in FR; [| exact MUc | exact WMc | cbn; clear - DRC CEIL LO' HDM; lia].
    step.
    ihere. to_implM.
    eapply (sqr_finish1 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s bs OW LB PL EA lo B jb jb st3 bs3 m3 m4 OW3 rr R ac Dr 96 qc 8%nat (sqr_comba4 la));
      [ exact ENV | exact LS | exact CEIL | exact GLO | exact LO | exact SPB | exact B63 | exact FROK | exact HR | exact HP | exact HPC | exact SR | exact ARR
      | apply to_limbs_limbs | apply to_limbs_length | fold br; clear - HDM; lia | lia | clear - LO'; lia
      | eapply munch_weaken; [| exact MUc]; unfold sub_fp; cbn [outside]; intros z Hz; clear - Hz; lia
      | exact WMc | exact MIc | exact STc | exact RES | exact FR ].
  Qed.

  Lemma sqr_path_comba8 : forall
      (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs) (lo B : Z)
      (jb : list byte) (st3 : PState) (bs3 : bstate bptr) (m3 : mem) (OW3 : list block) (rr rx : bnref) (R A ac : Z) (qc : bptr)
      (x1 t0 t1 t2 x8 a0 a1 a2 a3 a4 a5 a6 a7 x22 x23 t3 t4 t5 t6 : word),
    kenv LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -336) s bs OW m (sqr_frame jb ra s0 s1 s2 s3 s4 s5 s6 s7) st3 bs3 m3 OW3 ->
    lib_state bs3 m3 OW3 PL EA ->
    alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - BN_SQR_FIXED_STACK -> bv_unsigned sp <= B -> B < 2^63 -> frames_ok PL (bv_unsigned sp) B ->
    ref_at bs3 OW3 PL rr R -> hpl PL rr -> ref_at bs3 OW3 PL rx A -> rx <> ROne -> rx <> rr -> pl_ctx PL = Some (ac, qc) ->
    (8 <= bn_top (getbn rx bs3))%nat -> (16 <= bn_dmax (getbn rr bs3))%nat ->
    implM bgusegs (interp (embed (BN_CTX_end (tree_ops bptr)
              (setbn rr (sqr_fin (bn_with_buf (getbn rr bs3) (splice (bn_buf (getbn rr bs3)) 0 (sqr_comba8 (firstn 8 (bn_buf (getbn rx bs3)))))) 16) bs3)))) st3
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -336)) gp (wz RATP) t0 t1 t2 x8 (Z_to_bv 64 ac) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 R) (Z_to_bv 64 R) (Z_to_bv 64 (Z.of_nat 16)) (Z_to_bv 64 A) x22 x23 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1074a0) fc None m3 (seg_rom bgusegs)).
  Proof.
    intros until t6. intros ENV LS CEIL GLO LO SPB B63 FROK HR HP HX NX NXR HPC HAL HDM.
    pose proof LO as LO'. unfold BN_SQR_FIXED_STACK, BN_WEXPAND_STACK, BN_EXPAND2_STACK in LO'.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof ENV as (HEAP & _ & ST & _ & MI & _ & _ & _ & _ & FR & _). unfold sqr_frame in FR.
    destruct (open_full st3 OW3 LB m3 bs3 PL EA (bv_unsigned sp) B rr R HEAP LS FROK HR HP) as (Dr & SR & ARR & OKR & UR & R0 & RC & DR0 & DRC & DSEP).
    destruct (operand_view_ne st3 OW3 LB m3 bs3 PL EA (bv_unsigned sp) B rr R Dr rx A 8 HEAP LS FROK HR HP SR ARR HX NX HAL NXR)
      as (Dx & SX & LX & UX & ARX & X0 & XC & DX0 & DXC & XR & RDX & XDR & DRX).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HX) as HVX. pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS. pose proof PARTS as (WFS & _).
    pose proof (st_wf_ok rx bs3 WFS HVX NX) as (LMX & TDX & DMX & _). unfold BG_DMAX in DMX.
    pose proof (ref_at_ualign _ _ _ _ _ _ _ _ _ HEAP PARTS HR (proj1 HP)) as (_ & RAL).
    pose proof (bn_arr_ualign _ _ _ _ _ _ _ _ _ _ HEAP PARTS ARR ltac:(clear - HDM; lia)) as DRAL.
    pose proof (bn_arr_ualign _ _ _ _ _ _ _ _ _ _ HEAP PARTS ARX ltac:(clear - TDX HAL; unfold bn_dmax in *; lia)) as DXAL.
    set (br := getbn rr bs3) in *. set (bx := getbn rx bs3) in *. set (la := firstn 8 (bn_buf bx)) in *.
    assert (LLA : length la = 8%nat) by (unfold la; rewrite firstn_length_le; [reflexivity| unfold bn_dmax in TDX; lia]).
    assert (LIA : limbs la) by (apply limbs_firstn; exact LMX).
    pose proof (proj1 (limbarr_limbs_at bgusegs m3 Dr (bn_buf br)) UR) as [_ HW]. fold (bn_dmax br) in HW.
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -336)) = bv_unsigned sp + -336) by (apply unsigned_lit; lia).
    assert (EDr : bv_unsigned (Z_to_bv 64 Dr) = Dr) by (apply unsigned_lit; lia).
    assert (EDx : bv_unsigned (Z_to_bv 64 Dx) = Dx) by (apply unsigned_lit; clear - DX0 DXC CEIL LO' SPR; lia).
    pose proof SR as SR'. unfold bn_cells, MallocRep.wz in SR'. unfold MallocRep.wz in SX.
    unfold implM. iprefix.
    step. ub1 ub_kind.
    step. step. clear SR' SX.
    step.
    eapply evt_cut.
    { eapply sqr_comba8_ok with (a := la) (lo := lo) (m := m3); rewrite ?EDr, ?EDx, ?ESP; unfold HxSqr8.CSQ;
        [ exact LIA | exact LLA | exact LX | replace Dr with (Dr + 0) by lia; eapply wr_at_sub; [exact HW| | |]; clear - HDM; lia
        | clear - DRX HDM TDX HAL; unfold bn_dmax in *; lia | exact ST | clear - LO'; lia | clear - DRC CEIL LO'; lia | clear - DXC CEIL LO' TDX; unfold bn_dmax in *; lia | exact MI
        | intros _; exact DRAL | intros _; exact DXAL ]. }
    intros ms' PO. unfold W_mul_normal.vl_post in PO.
    destruct PO as (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m4 & E & MUc & WMc & MIc & RES & STc).
    subst ms'. rewrite ?EDr, ?ESP in *. unfold HxSqr8.CSQ in MUc.
    lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?r)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 r)) with (Z_to_bv 64 r) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.
    eapply (rw_cells_transport bgusegs _ m3 m4) in FR; [| exact MUc | exact WMc | cbn; clear - DRC CEIL LO' HDM; lia].
    step.
    ihere. to_implM.
    eapply (sqr_finish1 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s bs OW LB PL EA lo B jb jb st3 bs3 m3 m4 OW3 rr R ac Dr 256 qc 16%nat (sqr_comba8 la));
      [ exact ENV | exact LS | exact CEIL | exact GLO | exact LO | exact SPB | exact B63 | exact FROK | exact HR | exact HP | exact HPC | exact SR | exact ARR
      | apply to_limbs_limbs | apply to_limbs_length | fold br; clear - HDM; lia | lia | clear - LO'; lia
      | eapply munch_weaken; [| exact MUc]; unfold sub_fp; cbn [outside]; intros z Hz; clear - Hz; lia
      | exact WMc | exact MIc | exact STc | exact RES | exact FR ].
  Qed.

  Lemma sqr_path_ntmp : forall
      (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs) (lo B : Z)
      (jb : list byte) (st3 : PState) (bs3 : bstate bptr) (m3 : mem) (OW3 : list block) (rr rx t : bnref) (R A TT ac : Z) (qc : bptr) (al : nat)
      (x1 t0 t1 t2 x8 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    kenv LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -336) s bs OW m (sqr_frame jb ra s0 s1 s2 s3 s4 s5 s6 s7) st3 bs3 m3 OW3 ->
    lib_state bs3 m3 OW3 PL EA ->
    alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - BN_SQR_FIXED_STACK -> bv_unsigned sp <= B -> B < 2^63 -> frames_ok PL (bv_unsigned sp) B ->
    ref_at bs3 OW3 PL rr R -> hpl PL rr -> ref_at bs3 OW3 PL rx A -> rx <> ROne -> rx <> rr ->
    ref_at bs3 OW3 PL t TT -> hpl PL t -> t <> rr -> rx <> t -> pl_ctx PL = Some (ac, qc) ->
    (1 <= al <= bn_top (getbn rx bs3))%nat -> (2 * al <= bn_dmax (getbn rr bs3))%nat -> (2 * al <= bn_dmax (getbn t bs3))%nat ->
    implM bgusegs (interp (embed (BN_CTX_end (tree_ops bptr)
              (setbn rr (sqr_fin (bn_with_buf (getbn rr bs3) (splice (bn_buf (getbn rr bs3)) 0
                                    (fst (sqr_normal (firstn al (bn_buf (getbn rx bs3))) (firstn (2 * al) (bn_buf (getbn rr bs3))))))) (2 * al))
                 (setbn t (bn_with_buf (getbn t bs3) (splice (bn_buf (getbn t bs3)) 0 (sqr_words (firstn al (bn_buf (getbn rx bs3)))))) bs3))))) st3
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -336)) gp (wz RATP) t0 t1 t2 x8 (Z_to_bv 64 ac) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 R) (Z_to_bv 64 R) (Z_to_bv 64 (Z.of_nat (2 * al))) (Z_to_bv 64 A) (Z_to_bv 64 (Z.of_nat al)) (Z_to_bv 64 TT) s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x107558) fc None m3 (seg_rom bgusegs)).
  Proof.
    intros until t6. intros ENV LS CEIL GLO LO SPB B63 FROK HR HP HX NX NXR HT HPT NTR NXT HPC [HAL1 HAL] HDM HDT.
    pose proof LO as LO'. unfold BN_SQR_FIXED_STACK, BN_WEXPAND_STACK, BN_EXPAND2_STACK in LO'.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof ENV as (HEAP & _ & ST & _ & MI & _ & _ & _ & _ & FR & _). unfold sqr_frame in FR.
    pose proof (proj1 HP) as NRO. pose proof (proj1 HPT) as NROT.
    destruct (open_full st3 OW3 LB m3 bs3 PL EA (bv_unsigned sp) B rr R HEAP LS FROK HR HP) as (Dr & SR & ARR & OKR & UR & R0 & RC & DR0 & DRC & DSEP).
    destruct (open_full st3 OW3 LB m3 bs3 PL EA (bv_unsigned sp) B t TT HEAP LS FROK HT HPT) as (Dt & STT & ARRT & OKT & UT & T0 & TC & DT0 & DTC & DSEPT).
    destruct (operand_view_ne st3 OW3 LB m3 bs3 PL EA (bv_unsigned sp) B rr R Dr rx A al HEAP LS FROK HR HP SR ARR HX NX HAL NXR)
      as (Dx & SX & LX & UX & ARX & X0 & XC & DX0 & DXC & XR & RDX & XDR & DRX).
    pose proof (bn_arrs_disj st3 OW3 LB m3 bs3 PL EA (bv_unsigned sp) B rr t R TT Dr Dt HEAP LS FROK ltac:(congruence) HR HT NRO NROT ARR ARRT) as DRT.
    pose proof (bn_arrs_disj st3 OW3 LB m3 bs3 PL EA (bv_unsigned sp) B rx t A TT Dx Dt HEAP LS FROK NXT HX HT NX NROT ARX ARRT) as DXT.
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HX) as HVX. pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS. pose proof PARTS as (WFS & _).
    pose proof (st_wf_ok rx bs3 WFS HVX NX) as (LMX & TDX & DMX & _). unfold BG_DMAX in DMX.
    pose proof (ref_at_ualign _ _ _ _ _ _ _ _ _ HEAP PARTS HR NRO) as (_ & RAL).
    pose proof (ref_at_ualign _ _ _ _ _ _ _ _ _ HEAP PARTS HT NROT) as (_ & TAL).
    pose proof (bn_arr_ualign _ _ _ _ _ _ _ _ _ _ HEAP PARTS ARR ltac:(clear - HDM HAL1; lia)) as DRAL.
    pose proof (bn_arr_ualign _ _ _ _ _ _ _ _ _ _ HEAP PARTS ARX ltac:(clear - TDX HAL HAL1; unfold bn_dmax in *; lia)) as DXAL.
    pose proof (bn_arr_ualign _ _ _ _ _ _ _ _ _ _ HEAP PARTS ARRT ltac:(clear - HDT HAL1; lia)) as DTAL.
    destruct OKR as (LMR & _ & DMR & _). destruct OKT as (LMT & _ & DMT & _). unfold BG_DMAX in DMR, DMT.
    set (br := getbn rr bs3) in *. set (bx := getbn rx bs3) in *. set (tb := getbn t bs3) in *. set (la := firstn al (bn_buf bx)) in *.
    assert (LLA : length la = al) by (unfold la; rewrite firstn_length_le; [reflexivity| unfold bn_dmax in TDX; lia]).
    assert (LIA : limbs la) by (apply limbs_firstn; exact LMX).
    set (r0 := firstn (2 * al) (bn_buf br)).
    assert (LR0 : length r0 = (2 * al)%nat) by (unfold r0; rewrite firstn_length_le; [reflexivity| unfold bn_dmax in HDM; exact HDM]).
    assert (LIR0 : limbs r0) by (apply limbs_firstn; exact LMR).
    pose proof (proj1 (limbarr_split bgusegs m3 Dr (bn_buf br) (2 * al) ltac:(unfold bn_dmax in HDM; exact HDM)) UR) as [UR1 _].
    pose proof (proj1 (limbarr_limbs_at bgusegs m3 Dr r0) UR1) as [RR0 WR0]. rewrite LR0 in WR0.
    pose proof (proj1 (limbarr_limbs_at bgusegs m3 Dt (bn_buf tb)) UT) as [_ HWT]. fold (bn_dmax tb) in HWT.
    assert (AL31 : 2 * Z.of_nat al < 2147483648) by (clear - HDM DMR; lia).
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -336)) = bv_unsigned sp + -336) by (apply unsigned_lit; lia).
    assert (EDr : bv_unsigned (Z_to_bv 64 Dr) = Dr) by (apply unsigned_lit; lia).
    assert (EDt : bv_unsigned (Z_to_bv 64 Dt) = Dt) by (apply unsigned_lit; lia).
    assert (EDx : bv_unsigned (Z_to_bv 64 Dx) = Dx) by (apply unsigned_lit; clear - DX0 DXC CEIL LO' SPR; lia).
    assert (EAL : bv_unsigned (Z_to_bv 64 (Z.of_nat al)) = Z.of_nat al) by (apply unsigned_lit; clear - AL31; lia).
    pose proof SR as SR'. pose proof STT as STT'. unfold bn_cells, MallocRep.wz in SR', STT'. unfold MallocRep.wz in SX.
    unfold implM. iprefix.
    step. step. ub1 ub_kind.
    step. step. step. clear SR' SX STT'.
    step. step.
    eapply evt_cut.
    { eapply bn_sqr_normal_spec with (A := la) (r0 := r0) (lo := lo) (m := m3); rewrite ?EDr, ?EDx, ?EDt, ?ESP, ?EAL, ?LLA;
        [ exact LIA | exact LIR0 | exact LR0 | clear - HAL1; lia | exact AL31 | reflexivity | exact LX | exact RR0
        | replace (8 * (2 * Z.of_nat al)) with (8 * Z.of_nat (2 * al)) by lia; exact WR0
        | replace Dt with (Dt + 0) by lia; eapply wr_at_sub; [exact HWT| | |]; clear - HDT; lia
        | clear - DRX HDM TDX HAL; unfold bn_dmax in *; lia | clear - DRT HDM HDT; unfold bn_dmax in *; lia | clear - DXT HDT TDX HAL; unfold bn_dmax in *; lia
        | exact ST | clear - LO'; lia | clear - DRC CEIL LO' HDM; lia | clear - DXC CEIL LO' TDX HAL; unfold bn_dmax in *; lia | clear - DTC CEIL LO' HDT; lia | exact MI
        | intros _; exact DRAL | intros _; exact DXAL | intros _; exact DTAL ]. }
    intros ms' PO. unfold vl_post2 in PO.
    destruct PO as (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m4 & E & MUc & WMc & MIc & RES & REST & STc).
    subst ms'. rewrite ?EDr, ?EDt, ?ESP, ?LLA in *.
    lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?r)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 r)) with (Z_to_bv 64 r) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.
    eapply (rw_cells_transport bgusegs _ m3 m4) in FR; [| exact MUc | exact WMc | cbn; clear - DRC DTC CEIL LO' HDM HDT; lia].
    pose proof (sqr_normal_spec la LIA r0 ltac:(rewrite LLA; exact HAL1) LIR0 ltac:(rewrite LLA; exact LR0)) as SNS.
    destruct (sqr_normal la r0) as [ro to] eqn:ESN. destruct SNS as (LRO & LENRO & _ & ETO). cbn [fst] in RES |- *. rewrite LLA in LENRO.
    ihere. to_implM.
    eapply (sqr_finish2 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s bs OW LB PL EA lo B jb jb st3 bs3 m3 m4 OW3 rr t R TT ac Dr Dt 256 qc (2 * al)%nat ro (sqr_words la));
      [ exact ENV | exact LS | exact CEIL | exact GLO | exact LO | exact SPB | exact B63 | exact FROK | exact HR | exact HP | exact HT | exact HPT | exact NTR | exact HPC
      | exact SR | exact ARR | exact STT | exact ARRT
      | exact LRO | exact LENRO | fold br; clear - HDM HAL1; lia
      | apply sqr_words_limbs; exact LIA | rewrite sqr_words_length, LLA; fold tb; clear - HDT HAL1; lia | lia | clear - LO'; lia
      | rewrite sqr_words_length, LLA; eapply munch_weaken; [| exact MUc]; unfold sub_fp; cbn [outside]; intros z Hz; clear - Hz; lia
      | exact WMc | exact MIc | exact STc | exact RES | exact REST | exact FR ].
  Qed.

  Lemma sqr_path_rec : forall
      (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs) (lo B : Z)
      (jb : list byte) (st3 : PState) (bs3 : bstate bptr) (m3 : mem) (OW3 : list block) (rr rx t : bnref) (R A TT ac : Z) (qc : bptr) (k : nat)
      (x1 t0 t1 t2 x8 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    kenv LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -336) s bs OW m (sqr_frame jb ra s0 s1 s2 s3 s4 s5 s6 s7) st3 bs3 m3 OW3 ->
    lib_state bs3 m3 OW3 PL EA ->
    alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - BN_SQR_FIXED_STACK -> bv_unsigned sp <= B -> B < 2^63 -> frames_ok PL (bv_unsigned sp) B ->
    ref_at bs3 OW3 PL rr R -> hpl PL rr -> ref_at bs3 OW3 PL rx A -> rx <> ROne -> rx <> rr ->
    ref_at bs3 OW3 PL t TT -> hpl PL t -> t <> rr -> rx <> t -> pl_ctx PL = Some (ac, qc) ->
    (k <= 26)%nat -> (Nat.pow 2 k <= bn_top (getbn rx bs3))%nat -> (2 * Nat.pow 2 k <= bn_dmax (getbn rr bs3))%nat -> (sqr_scratch k <= bn_dmax (getbn t bs3))%nat ->
    implM bgusegs (interp (embed (BN_CTX_end (tree_ops bptr)
              (setbn rr (sqr_fin (bn_with_buf (getbn rr bs3) (splice (bn_buf (getbn rr bs3)) 0
                                    (fst (sqr_recursive k (firstn (Nat.pow 2 k) (bn_buf (getbn rx bs3))) (firstn (2 * Nat.pow 2 k) (bn_buf (getbn rr bs3))) (bn_buf (getbn t bs3)))))) (2 * Nat.pow 2 k))
                 (setbn t (bn_with_buf (getbn t bs3)
                                    (snd (sqr_recursive k (firstn (Nat.pow 2 k) (bn_buf (getbn rx bs3))) (firstn (2 * Nat.pow 2 k) (bn_buf (getbn rr bs3))) (bn_buf (getbn t bs3))))) bs3))))) st3
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -336)) gp (wz RATP) t0 t1 t2 x8 (Z_to_bv 64 ac) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 R) (Z_to_bv 64 R) (Z_to_bv 64 (Z.of_nat (2 * Nat.pow 2 k))) (Z_to_bv 64 A) (Z_to_bv 64 (Z.of_nat (Nat.pow 2 k))) (Z_to_bv 64 TT) s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x107524) fc None m3 (seg_rom bgusegs)).
  Proof.
    intros until t6. intros ENV LS CEIL GLO LO SPB B63 FROK HR HP HX NX NXR HT HPT NTR NXT HPC HK HAL HDM HDT. set (al := Nat.pow 2 k) in *. assert (HAL1 : (1 <= al)%nat) by (unfold al; clear; induction k; cbn; lia).
    pose proof LO as LO'. unfold BN_SQR_FIXED_STACK, BN_WEXPAND_STACK, BN_EXPAND2_STACK in LO'.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof ENV as (HEAP & _ & ST & _ & MI & _ & _ & _ & _ & FR & _). unfold sqr_frame in FR.
    pose proof (proj1 HP) as NRO. pose proof (proj1 HPT) as NROT.
    destruct (open_full st3 OW3 LB m3 bs3 PL EA (bv_unsigned sp) B rr R HEAP LS FROK HR HP) as (Dr & SR & ARR & OKR & UR & R0 & RC & DR0 & DRC & DSEP).
    destruct (open_full st3 OW3 LB m3 bs3 PL EA (bv_unsigned sp) B t TT HEAP LS FROK HT HPT) as (Dt & STT & ARRT & OKT & UT & T0 & TC & DT0 & DTC & DSEPT).
    destruct (operand_view_ne st3 OW3 LB m3 bs3 PL EA (bv_unsigned sp) B rr R Dr rx A al HEAP LS FROK HR HP SR ARR HX NX HAL NXR)
      as (Dx & SX & LX & UX & ARX & X0 & XC & DX0 & DXC & XR & RDX & XDR & DRX).
    pose proof (bn_arrs_disj st3 OW3 LB m3 bs3 PL EA (bv_unsigned sp) B rr t R TT Dr Dt HEAP LS FROK ltac:(congruence) HR HT NRO NROT ARR ARRT) as DRT.
    pose proof (bn_arrs_disj st3 OW3 LB m3 bs3 PL EA (bv_unsigned sp) B rx t A TT Dx Dt HEAP LS FROK NXT HX HT NX NROT ARX ARRT) as DXT.
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HX) as HVX. pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS. pose proof PARTS as (WFS & _).
    pose proof (st_wf_ok rx bs3 WFS HVX NX) as (LMX & TDX & DMX & _). unfold BG_DMAX in DMX.
    pose proof (ref_at_ualign _ _ _ _ _ _ _ _ _ HEAP PARTS HR NRO) as (_ & RAL).
    pose proof (ref_at_ualign _ _ _ _ _ _ _ _ _ HEAP PARTS HT NROT) as (_ & TAL).
    pose proof (bn_arr_ualign _ _ _ _ _ _ _ _ _ _ HEAP PARTS ARR ltac:(clear - HDM HAL1; lia)) as DRAL.
    pose proof (bn_arr_ualign _ _ _ _ _ _ _ _ _ _ HEAP PARTS ARX ltac:(clear - TDX HAL HAL1; unfold bn_dmax in *; lia)) as DXAL.
    pose proof (sqr_scratch_ge k) as SGE0. fold al in SGE0.
    pose proof (bn_arr_ualign _ _ _ _ _ _ _ _ _ _ HEAP PARTS ARRT ltac:(clear - HDT SGE0 HAL1; lia)) as DTAL. clear SGE0.
    destruct OKR as (LMR & _ & DMR & _). destruct OKT as (LMT & _ & DMT & _). unfold BG_DMAX in DMR, DMT.
    set (br := getbn rr bs3) in *. set (bx := getbn rx bs3) in *. set (tb := getbn t bs3) in *. set (la := firstn al (bn_buf bx)) in *.
    assert (LLA : length la = al) by (unfold la; rewrite firstn_length_le; [reflexivity| unfold bn_dmax in TDX; lia]).
    assert (LIA : limbs la) by (apply limbs_firstn; exact LMX).
    set (r0 := firstn (2 * al) (bn_buf br)).
    assert (LR0 : length r0 = (2 * al)%nat) by (unfold r0; rewrite firstn_length_le; [reflexivity| unfold bn_dmax in HDM; exact HDM]).
    assert (LIR0 : limbs r0) by (apply limbs_firstn; exact LMR).
    pose proof (proj1 (limbarr_split bgusegs m3 Dr (bn_buf br) (2 * al) ltac:(unfold bn_dmax in HDM; exact HDM)) UR) as [UR1 _].
    pose proof (proj1 (limbarr_limbs_at bgusegs m3 Dr r0) UR1) as [RR0 WR0]. rewrite LR0 in WR0.
    pose proof (proj1 (limbarr_limbs_at bgusegs m3 Dt (bn_buf tb)) UT) as [TT0 HWT].
    assert (LBT : length (bn_buf tb) = bn_dmax tb) by reflexivity.
    pose proof (sqr_scratch_ge k) as SGE. fold al in SGE.
    assert (AL31 : 2 * Z.of_nat al < 2147483648) by (clear - HDM DMR; lia).
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -336)) = bv_unsigned sp + -336) by (apply unsigned_lit; lia).
    assert (EDr : bv_unsigned (Z_to_bv 64 Dr) = Dr) by (apply unsigned_lit; lia).
    assert (EDt : bv_unsigned (Z_to_bv 64 Dt) = Dt) by (apply unsigned_lit; lia).
    assert (EDx : bv_unsigned (Z_to_bv 64 Dx) = Dx) by (apply unsigned_lit; clear - DX0 DXC CEIL LO' SPR; lia).
    assert (EAL : bv_unsigned (Z_to_bv 64 (Z.of_nat al)) = Z.of_nat al) by (apply unsigned_lit; clear - AL31; lia).
    pose proof SR as SR'. pose proof STT as STT'. unfold bn_cells, MallocRep.wz in SR', STT'. unfold MallocRep.wz in SX.
    unfold implM. iprefix.
    step. step. ub1 ub_kind.
    step. step. step. clear SR' SX STT'.
    step. step.
    assert (SRK : 0 <= srec_stack 256 k <= 3168) by (unfold srec_stack; clear - HK; lia).
    eapply evt_cut.
    { eapply (bn_sqr_recursive_spec 96 256 256 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) sqr_comba4_ok sqr_comba8_ok k) with (a := la) (R := r0) (T := bn_buf tb) (lo := lo) (m := m3);
        rewrite ?EDr, ?EDx, ?EDt, ?ESP, ?EAL, ?LLA, ?LR0, ?LBT;
        [ exact LIA | exact LIR0 | exact LMT | exact HK | reflexivity | reflexivity | exact HDT | reflexivity | exact LX | exact RR0 | exact TT0
        | exact WR0 | exact HWT
        | clear - DRX HDM TDX HAL; unfold bn_dmax in *; lia | clear - DXT HDT TDX HAL; unfold bn_dmax in *; lia | clear - DRT HDM HDT; unfold bn_dmax in *; lia
        | exact ST | clear - LO' SRK; lia | clear - DRC CEIL LO' HDM SRK; lia | clear - DTC CEIL LO' HDT SRK; lia | clear - DXC CEIL LO' TDX HAL SRK; unfold bn_dmax in *; lia | exact MI
        | intros _; exact DRAL | intros _; exact DXAL | intros _; exact DTAL ]. }
    intros ms' PO. unfold W_mul_recursive.kr_post in PO.
    destruct PO as (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m4 & E & MUc & WMc & MIc & RES & REST & STc).
    subst ms'. rewrite ?EDr, ?EDt, ?ESP, ?LLA, ?LR0, ?LBT in *.
    lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?r)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 r)) with (Z_to_bv 64 r) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.
    eapply (rw_cells_transport bgusegs _ m3 m4) in FR; [| exact MUc | exact WMc | cbn; clear - DRC DTC CEIL LO' HDM HDT SRK; lia].
    pose proof (sqr_recursive_spec k la r0 (bn_buf tb) LIA LIR0 LMT LLA LR0 ltac:(rewrite LBT; exact HDT)) as SNS. unfold sqr_post in SNS.
    destruct (sqr_recursive k la r0 (bn_buf tb)) as [ro to] eqn:ESN. destruct SNS as (LRO & LENRO & _ & LTO & LENTO). cbn [fst snd] in RES, REST |- *. rewrite LR0 in LENRO. rewrite LBT in LENTO.
    replace (bn_with_buf tb to) with (bn_with_buf tb (splice (bn_buf tb) 0 to)) by (rewrite splice_full by (rewrite LBT; exact LENTO); reflexivity).
    step.
    ihere. to_implM.
    eapply (sqr_finish2 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s bs OW LB PL EA lo B jb jb st3 bs3 m3 m4 OW3 rr t R TT ac Dr Dt (srec_stack 256 k) qc (2 * al)%nat ro to);
      [ exact ENV | exact LS | exact CEIL | exact GLO | exact LO | exact SPB | exact B63 | exact FROK | exact HR | exact HP | exact HT | exact HPT | exact NTR | exact HPC
      | exact SR | exact ARR | exact STT | exact ARRT
      | exact LRO | exact LENRO | fold br; clear - HDM HAL1; lia
      | exact LTO | rewrite LENTO; fold tb; clear - HDT SGE HAL1; lia | clear - SRK; lia | clear - LO' SRK; lia
      | rewrite LENTO; eapply munch_weaken; [| exact MUc]; unfold sub_fp; cbn [outside]; intros z Hz; clear - Hz SRK; lia
      | exact WMc | exact MIc | exact STc | exact RES | exact REST | exact FR ].
  Qed.

  Lemma sqr_path_stack : forall
      (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs) (lo B : Z)
      (jb : list byte) (st3 : PState) (bs3 : bstate bptr) (m3 : mem) (OW3 : list block) (rr rx : bnref) (R A ac : Z) (qc : bptr) (al : nat)
      (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x23 t3 t4 t5 t6 : word),
    kenv LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -336) s bs OW m (sqr_frame jb ra s0 s1 s2 s3 s4 s5 s6 s7) st3 bs3 m3 OW3 ->
    lib_state bs3 m3 OW3 PL EA ->
    alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - BN_SQR_FIXED_STACK -> bv_unsigned sp <= B -> B < 2^63 -> frames_ok PL (bv_unsigned sp) B ->
    ref_at bs3 OW3 PL rr R -> hpl PL rr -> ref_at bs3 OW3 PL rx A -> rx <> ROne -> rx <> rr -> pl_ctx PL = Some (ac, qc) ->
    (1 <= al <= bn_top (getbn rx bs3))%nat -> (al < 16)%nat -> (2 * al <= bn_dmax (getbn rr bs3))%nat -> bv_unsigned sp mod 16 = 0 ->
    implM bgusegs (interp (embed (BN_CTX_end (tree_ops bptr)
              (setbn rr (sqr_fin (bn_with_buf (getbn rr bs3) (splice (bn_buf (getbn rr bs3)) 0
                                    (fst (sqr_normal (firstn al (bn_buf (getbn rx bs3))) (firstn (2 * al) (bn_buf (getbn rr bs3))))))) (2 * al)) bs3)))) st3
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -336)) gp (wz RATP) t0 t1 t2 sp (Z_to_bv 64 ac) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 R) (Z_to_bv 64 R) (Z_to_bv 64 (Z.of_nat (2 * al))) (Z_to_bv 64 A) (Z_to_bv 64 (Z.of_nat al)) x23 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1074c0) fc None m3 (seg_rom bgusegs)).
  Proof.
    intros until t6. intros ENV LS CEIL GLO LO SPB B63 FROK HR HP HX NX NXR HPC [HAL1 HAL] HAL16 HDM SP16.
    pose proof LO as LO'. unfold BN_SQR_FIXED_STACK, BN_WEXPAND_STACK, BN_EXPAND2_STACK in LO'.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof ENV as (HEAP & _ & ST & _ & MI & _ & _ & _ & _ & FR & _). unfold sqr_frame in FR.
    pose proof (proj1 HP) as NRO.
    destruct (open_full st3 OW3 LB m3 bs3 PL EA (bv_unsigned sp) B rr R HEAP LS FROK HR HP) as (Dr & SR & ARR & OKR & UR & R0 & RC & DR0 & DRC & DSEP).
    destruct (operand_view_ne st3 OW3 LB m3 bs3 PL EA (bv_unsigned sp) B rr R Dr rx A al HEAP LS FROK HR HP SR ARR HX NX HAL NXR)
      as (Dx & SX & LX & UX & ARX & X0 & XC & DX0 & DXC & XR & RDX & XDR & DRX).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HX) as HVX. pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS. pose proof PARTS as (WFS & _).
    pose proof (st_wf_ok rx bs3 WFS HVX NX) as (LMX & TDX & DMX & _). unfold BG_DMAX in DMX.
    pose proof (ref_at_ualign _ _ _ _ _ _ _ _ _ HEAP PARTS HR NRO) as (_ & RAL).
    pose proof (bn_arr_ualign _ _ _ _ _ _ _ _ _ _ HEAP PARTS ARR ltac:(clear - HDM HAL1; lia)) as DRAL.
    pose proof (bn_arr_ualign _ _ _ _ _ _ _ _ _ _ HEAP PARTS ARX ltac:(clear - TDX HAL HAL1; unfold bn_dmax in *; lia)) as DXAL.
    assert (TAL : 0 < bv_unsigned sp + -328 /\ (bv_unsigned sp + -328) mod 8 = 0) by (split; [lia | clear - SP16; Z.div_mod_to_equations; lia]).
    destruct OKR as (LMR & _ & DMR & _). unfold BG_DMAX in DMR.
    set (br := getbn rr bs3) in *. set (bx := getbn rx bs3) in *. set (la := firstn al (bn_buf bx)) in *.
    assert (LLA : length la = al) by (unfold la; rewrite firstn_length_le; [reflexivity| unfold bn_dmax in TDX; lia]).
    assert (LIA : limbs la) by (apply limbs_firstn; exact LMX).
    set (r0 := firstn (2 * al) (bn_buf br)).
    assert (LR0 : length r0 = (2 * al)%nat) by (unfold r0; rewrite firstn_length_le; [reflexivity| unfold bn_dmax in HDM; exact HDM]).
    assert (LIR0 : limbs r0) by (apply limbs_firstn; exact LMR).
    pose proof (proj1 (limbarr_split bgusegs m3 Dr (bn_buf br) (2 * al) ltac:(unfold bn_dmax in HDM; exact HDM)) UR) as [UR1 _].
    pose proof (proj1 (limbarr_limbs_at bgusegs m3 Dr r0) UR1) as [RR0 WR0]. rewrite LR0 in WR0.
    assert (AL31 : 2 * Z.of_nat al < 2147483648) by (clear - HAL16; lia).

    apply (proj1 (bk_rw_cells_app bgusegs m3 (bv_unsigned sp + -336) [CB 264 jb] [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])) in FR.
    destruct FR as [FRa FRb]. cbn [cells_size csize Nat.add] in FRb.
    pose proof (stk_of_rw_cells bgusegs _ _ _ FRa) as STK264. cbn [cells_size csize Nat.add] in STK264.
    assert (WT : wr_at bgusegs m3 (bv_unsigned sp + -328) (8 * (2 * Z.of_nat al))).
    { destruct STK264 as (S1 & S2 & S3). split; [clear - LO' CEIL; lia|]. split; [clear - SPR HAL16; lia|].
      intros i Hi. apply (S3 (bv_unsigned sp + -328 + i)). clear - Hi HAL16. lia. }
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -336)) = bv_unsigned sp + -336) by (apply unsigned_lit; lia).
    assert (EST : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -328)) = bv_unsigned sp + -328) by (apply unsigned_lit; lia).
    assert (EDr : bv_unsigned (Z_to_bv 64 Dr) = Dr) by (apply unsigned_lit; lia).
    assert (EDx : bv_unsigned (Z_to_bv 64 Dx) = Dx) by (apply unsigned_lit; clear - DX0 DXC CEIL LO' SPR; lia).
    assert (EAL : bv_unsigned (Z_to_bv 64 (Z.of_nat al)) = Z.of_nat al) by (apply unsigned_lit; clear - AL31; lia).
    pose proof SR as SR'. unfold bn_cells, MallocRep.wz in SR'. unfold MallocRep.wz in SX.
    unfold implM. iprefix.
    step. ub1 ub_kind.
    step. step. clear SR' SX.
    step. step. step. step.
    eapply evt_cut.
    { eapply bn_sqr_normal_spec with (A := la) (r0 := r0) (lo := lo) (m := m3); rewrite ?EDr, ?EDx, ?EST, ?ESP, ?EAL, ?LLA;
        [ exact LIA | exact LIR0 | exact LR0 | clear - HAL1; lia | exact AL31 | reflexivity | exact LX | exact RR0
        | replace (8 * (2 * Z.of_nat al)) with (8 * Z.of_nat (2 * al)) by lia; exact WR0
        | exact WT
        | clear - DRX HDM TDX HAL; unfold bn_dmax in *; lia | clear - DRC CEIL LO' HDM; lia | clear - DXC CEIL LO' HAL16 TDX HAL; unfold bn_dmax in *; lia
        | exact ST | clear - LO'; lia | clear - DRC CEIL LO' HDM; lia | clear - DXC CEIL LO' TDX HAL; unfold bn_dmax in *; lia | right; clear; lia | exact MI
        | intros _; exact DRAL | intros _; exact DXAL | intros _; exact TAL ]. }
    intros ms' PO. unfold vl_post2 in PO.
    destruct PO as (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m4 & E & MUc & WMc & MIc & RES & REST & STc).
    subst ms'. rewrite ?EDr, ?EST, ?ESP, ?LLA in *.
    lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?r)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 r)) with (Z_to_bv 64 r) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.

    eapply (rw_cells_transport bgusegs _ m3 m4) in FRb; [| exact MUc | exact WMc | cbn; clear - DRC CEIL LO' HDM HAL16; lia].
    assert (UT4 : u64arr bgusegs m4 (bv_unsigned sp + -328) (wlimbs (sqr_words la))).
    { apply u64arr_of_limbs_at; [exact REST|]. rewrite sqr_words_length, LLA. eapply wr_at_transport; [| exact WMc].
      replace (8 * Z.of_nat (2 * al)) with (8 * (2 * Z.of_nat al)) by lia. exact WT. }
    apply limbarr_CB in UT4. rewrite sqr_words_length, LLA in UT4.
    assert (STK4 : stk bgusegs m4 (bv_unsigned sp + -336) (bv_unsigned sp + -336 + 264)).
    { eapply (W_ctx3.stk_transport_rw _ m3 m4); [exact STK264 | exact MUc | exact WMc | exact UT4 |].
      intros x Hx. cbn [cells_size csize Nat.add outside].
      destruct (Z_lt_ge_dec x (bv_unsigned sp + -328)) as [L|G]; [left; clear - L Hx DRC CEIL LO' HDM; lia|].
      destruct (Z_lt_ge_dec x (bv_unsigned sp + -328 + 8 * (2 * Z.of_nat al))) as [L2|G2]; [right; clear - G L2; lia| left; clear - G2 Hx DRC CEIL LO' HDM; lia]. }
    destruct (stk_carve bgusegs m4 (bv_unsigned sp + -336) (bv_unsigned sp + -336 + 264) 264 STK4 ltac:(clear; lia)) as [_ [jb' FRa4]].
    replace (bv_unsigned sp + -336 + 264 - Z.of_nat 264) with (bv_unsigned sp + -336) in FRa4 by (clear; lia).
    assert (FR4 : rw_cells bgusegs m4 (bv_unsigned sp + -336) (sqr_frame jb' ra s0 s1 s2 s3 s4 s5 s6 s7)).
    { unfold sqr_frame. apply (proj2 (bk_rw_cells_app bgusegs m4 (bv_unsigned sp + -336) [CB 264 jb'] [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
      split; [exact FRa4|]. cbn [cells_size csize Nat.add]. exact FRb. }
    pose proof (sqr_normal_spec la LIA r0 ltac:(rewrite LLA; exact HAL1) LIR0 ltac:(rewrite LLA; exact LR0)) as SNS.
    destruct (sqr_normal la r0) as [ro to] eqn:ESN. destruct SNS as (LRO & LENRO & _ & ETO). cbn [fst] in RES |- *. rewrite LLA in LENRO.
    ihere. to_implM.
    eapply (sqr_finish1 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s bs OW LB PL EA lo B jb jb' st3 bs3 m3 m4 OW3 rr R ac Dr 256 qc (2 * al)%nat ro);
      [ exact ENV | exact LS | exact CEIL | exact GLO | exact LO | exact SPB | exact B63 | exact FROK | exact HR | exact HP | exact HPC | exact SR | exact ARR
      | exact LRO | exact LENRO | fold br; clear - HDM HAL1; lia | lia | clear - LO'; lia
      | eapply munch_weaken; [| exact MUc]; unfold sub_fp; cbn [outside]; intros z Hz; clear - Hz HAL16; lia
      | exact WMc | exact MIc | exact STc | exact RES | exact FR4 ].
  Qed.

  Lemma bn_sqr_fixed_top_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (rr rx : bnref) (ar ax ac : Z) (qc : bptr),
    bn_pre s bs m OW LB PL EA sp lo B errv BN_SQR_FIXED_STACK -> tp = wz RATP -> bv_unsigned sp mod 16 = 0 ->
    ref_at bs OW PL rr ar -> ref_at bs OW PL rx ax -> hpl PL rr -> rx <> ROne -> pl_ctx PL = Some (ac, qc) ->
    a0 = wz ar -> a1 = wz ax -> a2 = wz ac ->
    implM bgusegs (interp (embed (bn_sqr_fixed_top (tree_ops bptr) rr rx bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_SQR_FIXED_TOP) fc None m (seg_rom bgusegs)).
  Proof.
    intros until qc. intros PRE -> SP16 HR HX HP NX HPC -> -> ->. pose proof (proj1 HP) as NRO.
    pose proof PRE as (HEAP & LS & FROK & AUX & SPB & B63 & ST & CEIL & GLO & LO & ERR & MI).
    pose proof LO as LO'. unfold BN_SQR_FIXED_STACK, BN_WEXPAND_STACK, BN_EXPAND2_STACK in LO'.
    unfold BN_SQR_FIXED_TOP, MallocRep.wz.

    unfold bn_sqr_fixed_top. rewrite bn_live_run.
    destruct (live_refs (st_ctx bs) [rr; rx]) eqn:LIVE; [| cbn [embed interp]; apply implM_interp_unr]. apply live_refs_true_iff in LIVE.
    pose proof (Forall_inv LIVE) as LVR. pose proof (Forall_inv (Forall_inv_tail LIVE)) as LVX. clear LIVE.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS; pose proof PARTS as (WFS & PWF & IDS & PLB & ERRB).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HR) as HVR. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HX) as HVX.
    destruct (open_ro s OW LB m bs PL EA (bv_unsigned sp) B rx ax HEAP LS FROK HX NX) as (Dx0 & SX & OKX & _ & X0 & XC & _).
    pose proof OKX as (LMX & TDX & DMX & _). unfold BG_DMAX in DMX.
    pose proof (ref_at_hrange _ _ _ _ _ _ _ _ _ HEAP PARTS HR HP) as (SA0 & SAC & SAI & (qs & As & ns & Hins & Ra1 & Ra2)).
    assert (ArR : 0 < ar < 2^64) by (clear - SA0 SAC CEIL LO' SPR; lia).
    assert (AxR : 0 < ax < 2^64) by (clear - X0 XC CEIL LO' SPR B63 SPB; lia).
    pose proof (ref_at_ualign _ _ _ _ _ _ _ _ _ HEAP PARTS HR NRO) as (_ & ARAL).
    pose proof (ref_at_ualign _ _ _ _ _ _ _ _ _ HEAP PARTS HX NX) as (_ & AXAL).
    set (a := getbn rx bs) in *. set (al := bn_top a) in *.
    unfold bn_cells, MallocRep.wz in SX.
    pose proof (munch_refl [(bv_unsigned sp - 336, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgusegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3346328 - 164) with 3346164 in ERR.
    assert (GLO' : GLOBALS_TOP <= lo) by exact GLO. unfold GLOBALS_TOP in GLO.
    unfold bbind, bget, bset, bret. cbn [bind ret tree_ops tbind fst snd]. fold a. fold al.
    unfold implM. iprefix.
    carve_frame 336%nat ST. do 11 step.
    ub1 ub_kind. step. step. step. ub1 ub_kind.
    step. rewrite (sx32_small (Z.of_nat al)) by (clear - TDX DMX; unfold al, bn_dmax in *; lia).
    step. rewrite lts_signed by (clear - TDX DMX; unfold al, bn_dmax in *; lia).
    destruct (Z.ltb_spec 0 (Z.of_nat al)) as [ALP|ALZ]; cbn [negb].
    2:{
      replace (al =? 0)%nat with true by (symmetry; apply Nat.eqb_eq; clear - ALZ; lia).
      clear SX.
      ihere. to_implM. cbn [embed interp]. apply implM_ret.
      destruct (lib_state_open [] bs m OW PL EA rr ar LS ND HR ltac:(intros []) NRO) as ((Dr & SR & ARR) & OKR & LSH).
      destruct (bn_arr_facts_w bs OW PL EA (bv_unsigned sp) B s LB m rr Dr HEAP PARTS FROK HVR (hpl_wref PL rr HP) ARR) as (U & LENW & D0 & DC & DI & DSEP).
      specialize (DSEP rr ar HR).
      set (b := getbn rr bs) in *.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
      eapply (rw_cells_transport bgusegs _ m m1) in SR; [| exact MU | exact WM | cbn; clear - SAC CEIL LO'; lia].
      eapply (u64arr_transport bgusegs _ m m1) in U; [| exact MU | exact WM | cbn [disjoint_from]; rewrite wlimbs_len; fold (bn_dmax b); clear - DC CEIL LO'; lia].
      assert (MU1 : munch [(bv_unsigned sp - 336, bv_unsigned sp); (ar, ar + 24)]%Z m m1).
      { eapply munch_weaken; [| exact MU]. unfold sub_fp; cbn [outside]; intros z Hz; clear - Hz; lia. }
      clear MU. unfold bn_cells, MallocRep.wz in SR.
      ub1 ub_kind. step. ub1 ub_kind.
      step. step. step. step.
      step. do 9 step. release_frame FR ST (bv_unsigned sp). step. step.
      apply evt_done.
      lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mF end.
      assert (HWL : Forall (w_lib bs OW PL lo (bv_unsigned sp)) [(bv_unsigned sp - 336, bv_unsigned sp); (ar, ar + 24)]).
      { constructor; [left; cbn; lia|]. constructor; [right; left; exists (qs, As, ns); cbn [blk_addr blk_size fst snd]; split; [exact Hins | lia] | constructor]. }
      assert (WOK : Forall (w_ok OW LB bs PL EA (bv_unsigned sp) [rr]) [(bv_unsigned sp - 336, bv_unsigned sp); (ar, ar + 24)]).
      { constructor; [apply w_stack; cbn; lia|]. constructor; [eapply (w_struct OW LB bs PL EA (bv_unsigned sp) false [rr] _ rr ar); [left; reflexivity | exact HR | exact NRO | cbn; lia | cbn; lia] | constructor]. }
      unfold bn_post. do 15 eexists. exists mF, OW, PL, errv. split; [reflexivity|]. cbn [fst snd].
      split; [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU1 WM HWL CEIL)|].
      split.
      { unfold lib_state. eapply (lib_state_close [] bs mF OW PL EA rr ar); [| exact ND | exact HR | exact NRO | | |].
        - eapply (lib_state_frame s LB (bv_unsigned sp) B); [exact HEAP| exact LSH| exact MU1| exact WM| exact FROK| exact WOK].
        - exists Dr. split; [unfold bn_cells, bn_dmax; cbn [bn_top bn_buf bn_neg bn_flags Z.b2z]; exact SR|].
          eapply bn_arr_of_u64arr; [exact ARR | exact U].
        - destruct OKR as (O1 & O2 & O3 & O4). unfold bg_ok, bn_dmax in *. cbn [bn_top bn_buf bn_flags]. repeat split; [exact O1 | lia | exact O3 | exact O4].
        - apply ids_ok_setbn_same; [exact IDS | exact HVR | reflexivity]. }
      split; [apply (seg_auxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK AUX MU1 WM HWL SPB ltac:(lia)); unfold GLOBALS_TOP; lia|].
      split; [exact ST|]. split; [unfold LX_ERRNO, RATP; exact ERR|]. split; [exact MI|].
      split; [apply (seg_lx_pres _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU1 WM HWL CEIL); unfold GLOBALS_TOP; lia|].
      split; [reflexivity|]. split; [reflexivity|]. split; [apply refs_stable_setbn|]. split; reflexivity. }
    replace (al =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; clear - ALP; lia).

    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HWL : Forall (w_lib bs OW PL lo (bv_unsigned sp)) [(bv_unsigned sp - 336, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
    assert (WOK : Forall (w_ok OW LB bs PL EA (bv_unsigned sp) []) [(bv_unsigned sp - 336, bv_unsigned sp)]) by (constructor; [apply w_stack; cbn; lia| constructor]).
    pose proof (lib_state_frame s LB _ _ [] bs m m1 OW PL EA _ HEAP LS MU WM FROK WOK) as LS1.
    lazymatch type of FR with rw_cells _ _ _ (CB 264 ?jb0 :: _) =>
      assert (ENV : kenv LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -336) s bs OW m (sqr_frame jb0 ra s0 s1 s2 s3 s4 s5 s6 s7) s bs m1 OW)
    end.
    { unfold kenv, sqr_frame. split; [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL)|].
      split; [apply (seg_auxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK AUX MU WM HWL SPB ltac:(lia)); exact GLO'|].
      split; [exact ST|]. split; [exists errv; unfold LX_ERRNO, RATP; exact ERR|]. split; [exact MI|].
      split; [apply (seg_lx_pres _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL); lia|].
      split; [reflexivity|]. split; [reflexivity|]. split; [apply refs_stable_refl|]. split; [exact FR| cbn; lia]. }
    assert (FBlo : lo <= bv_unsigned sp + -336) by lia.
    assert (FBsp : bv_unsigned sp + -336 <= bv_unsigned sp) by lia.
    assert (SPR2 : bv_unsigned sp < 2 ^ 64) by lia.
    pose proof (kenv_pre LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -336) s bs OW m CEIL GLO' FBlo FBsp SPB B63 SPR2 FROK) as KPRE.
    pose proof (kenv_post LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -336) s bs OW m CEIL GLO' FBlo FBsp FROK) as KPOST.
    pose proof (fun A => @bn_post_kpost _ _ LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -336) CEIL FBlo FBsp SPR2 A) as BPK.
    assert (LOF : lo <= bv_unsigned sp + -336 - BN_WEXPAND_STACK) by (unfold BN_WEXPAND_STACK, BN_EXPAND2_STACK; lia).
    clear AUX ST ERR MI MU WM HWL WOK FR SX PRE.

    step. step.
    destruct (KPRE _ _ _ _ _ BN_CTX_START_STACK ENV LS1 ltac:(unfold BN_CTX_START_STACK; clear - LO'; lia)) as (errv1 & PRE1).
    step.
    ihere. to_implM.
    eapply implM_embed_bind.
    { eapply BnLeaves.implM_embed_leaves; [apply BN_CTX_start_leaves|].
      first [eapply (BN_CTX_start_walk HM HF) | eapply (BN_CTX_start_walk HM)]; [exact PRE1| reflexivity| exact HPC| reflexivity]. }
    cbv beta. intros [u1 bs1] st1 ms1 [PO LF1]. apply BPK in PO; [|intros v9 b9 o9 p9 a9 [E _]; exact E].
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & OW2 & -> & KP & (_ & INCL2)).
    destruct (KPOST _ _ _ _ _ _ _ _ _ ENV KP) as (ENV2 & LS2). pose proof KP as RS2; apply kpost_refs in RS2.
    cbn [fst snd] in *. clear PRE1 KP ENV LS1.
    replace (ret_pc (Z_to_bv 64 1078288)) with (Z_to_bv 64 1078288) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    destruct LF1 as (LB1 & LP1 & LU1 & LI1).
    pose proof (ref_at_stable _ _ _ _ PL _ _ RS2 HR) as HR2. pose proof (ref_at_stable _ _ _ _ PL _ _ RS2 HX) as HX2.

    destruct (Nat.eq_dec rr rx) as [EQ|NRX].
    { subst rx. rewrite Nat.eqb_refl. unfold bunr. cbn [unreachable tree_ops tbind embed interp]. apply implM_interp_unr. }
    replace (rr =? rx)%nat with false by (symmetry; apply Nat.eqb_neq; exact NRX).
    pose proof ENV2 as (HEAP2 & _).
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS2) as PARTS2.
    assert (FROK2 : frames_ok PL (bv_unsigned sp + -336) B) by (eapply frames_ok_call; [exact FROK| exact CEIL| exact FBlo| exact FBsp]).
    pose proof (struct_disj st1 OW2 LB m2 HEAP2 bs1 PL EA _ _ PARTS2 FROK2 rr rx ar ax NRX HR2 HX2) as SDJ.
    unfold implM. iprefix.
    step. step. if_cases KE; rewrite ?unsigned_lit in KE by (clear - ArR AxR; lia); zify_cond KE; [| exfalso; clear - KE SDJ; lia]. clear KE.

    step.
    destruct (KPRE _ _ _ _ _ BN_CTX_GET_STACK ENV2 LS2 ltac:(unfold BN_CTX_GET_STACK; clear - LO'; lia)) as (errv2 & PRE2).
    step.
    ihere. to_implM.
    apply BnAssoc.implM_embed_assoc.
    pose proof (st_wf_get_pre bs1 (proj1 PARTS2)) as (GP1 & GP2 & GP3).
    eapply implM_embed_bind.
    { eapply BnLeaves.implM_embed_leaves; [apply (BN_CTX_get_leaves bs1 GP1 GP2)|].
      first [eapply (BN_CTX_get_walk HM HF) | eapply (BN_CTX_get_walk HM)]; [exact PRE2| reflexivity| exact HPC| reflexivity]. }
    cbv beta. intros [t bs2] st2 ms2 [PO LF2]. apply BPK in PO; [|intros v9 b9 o9 p9 a9 [E _]; exact E].
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m3 & OW3 & -> & KP & (_ & (ti & Et) & (at_ & HAt & ->) & INCL3)).
    destruct (KPOST _ _ _ _ _ _ _ _ _ ENV2 KP) as (ENV3 & LS3). pose proof KP as RS3; apply kpost_refs in RS3.
    cbn [fst snd] in *. clear PRE2 KP ENV2 LS2.
    replace (ret_pc (Z_to_bv 64 1078316)) with (Z_to_bv 64 1078316) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    destruct LF2 as (LT1 & LT2 & LT3 & LT4 & LT5 & LT6). cbn [fst snd] in *. unfold MallocRep.wz.

    pose proof (refs_stable_trans _ _ _ _ _ _ RS2 RS3) as RS13.
    pose proof (ref_at_stable _ _ _ _ PL _ _ RS13 HR) as HR3. pose proof (ref_at_stable _ _ _ _ PL _ _ RS13 HX) as HX3.
    assert (ETU : t = RPool (gx_used (st_ctx bs))) by (rewrite LT1, GP3, LU1; reflexivity).
    assert (NTR : t <> rr) by (rewrite ETU; clear - LVR; unfold RPool; lia).
    assert (NXT : rx <> t) by (rewrite ETU; clear - LVX; unfold RPool; lia).
    assert (HPT : hpl PL t) by (rewrite Et; apply hpl_pool).
    assert (EB1 : forall r, getbn r bs1 = getbn r bs) by (intros r; unfold getbn; rewrite LB1; reflexivity).
    assert (EA2 : getbn rx bs2 = a) by (rewrite LT4 by (rewrite <- LT1; exact NXT); apply EB1).
    assert (ER2 : getbn rr bs2 = getbn rr bs) by (rewrite LT4 by (rewrite <- LT1; intros E; apply NTR; symmetry; exact E); apply EB1).
    pose proof ENV3 as (HEAP3 & _). pose proof (RH_nodup_l _ _ _ _ HEAP3) as ND3. pose proof (lib_state_h_parts _ _ _ _ _ _ LS3) as PARTS3.
    pose proof (ref_at_hrange _ _ _ _ _ _ _ _ _ HEAP3 PARTS3 HAt HPT) as (At0 & AtC & _).
    assert (AtR : 0 < at_ < 2^64) by (clear - At0 AtC CEIL LO' SPR; lia). clear AtC.
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS3 HR3) as HVR3.
    pose proof (st_wf_ok rr bs2 (proj1 PARTS3) HVR3 NRO) as (_ & TDR2 & _).
    assert (AL512 : Z.of_nat al <= 512) by (clear - TDX DMX; unfold al, bn_dmax in *; lia).
    unfold implM. iprefix.
    step. step. if_cases KZ; rewrite ?unsigned_lit in KZ by (clear - ArR; lia); zify_cond KZ; [exfalso; clear - KZ ArR; lia| clear KZ].
    step. step. if_cases KZ; rewrite ?unsigned_lit in KZ by (clear - AtR; lia); zify_cond KZ; [exfalso; clear - KZ AtR; lia| clear KZ].
    step. step. ub1 ub_kind.
    step. setreg 20%Z (Z_to_bv 64 (Z.of_nat (2 * al))) ltac:(f_equal; rewrite (unsigned_lit (Z.of_nat al)) by (clear - AL512; lia); rewrite Z.shiftl_mul_pow2 by lia; rewrite bn_swrap32_small by (clear - AL512; lia); lia).

    step. step.
    destruct (KPRE _ _ _ _ _ BN_WEXPAND_STACK ENV3 LS3 LOF) as (errv3 & PRE3).
    step.
    ihere. to_implM.
    apply BnAssoc.implM_embed_assoc.
    eapply implM_embed_bind.
    { eapply BnLeaves.implM_embed_leaves; [apply (bn_wexpand_leaves2 rr (2 * al) bs2 HVR3 TDR2)|].
      eapply (bn_wexpand_walk HM HF) with (r := rr) (a := ar) (words := (2 * al)%nat);
        [exact PRE3 | reflexivity | exact HR3 | exact (hpl_wref PL rr HP) | reflexivity | reflexivity | clear - AL512; lia]. }
    cbv beta. intros [u4 bs3] st3 ms3 [PO LF3]. apply BPK in PO; [|intros v9 b9 o9 p9 a9 [E _]; exact E].
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m4 & OW4 & -> & KP & (_ & -> & HDM & WRES & BST4)).
    destruct (KPOST _ _ _ _ _ _ _ _ _ ENV3 KP) as (ENV4 & LS4). pose proof KP as RS4; apply kpost_refs in RS4.
    cbn [fst snd] in *. clear PRE3 KP ENV3 LS3.
    replace (ret_pc (Z_to_bv 64 1078360)) with (Z_to_bv 64 1078360) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    destruct LF3 as (LW1 & LW2 & LW3 & LW4 & LW5 & LW6 & LW7 & LW8). cbn [fst snd] in *. unfold MallocRep.wz.
    pose proof (ref_at_stable _ _ _ _ PL _ _ RS4 HR3) as HR4. pose proof (ref_at_stable _ _ _ _ PL _ _ RS4 HX3) as HX4. pose proof (ref_at_stable _ _ _ _ PL _ _ RS4 HAt) as HT4.
    assert (EA4 : getbn rx bs3 = a) by (rewrite LW1 by (intros E; apply NRX; exact E); exact EA2).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS4 HR4) as HVR4.
    assert (ALT : (al <= bn_top (getbn rx bs3))%nat) by (rewrite EA4; unfold al; clear; lia).
    unfold implM. iprefix.
    step. if_cases KZ; rewrite ?unsigned_lit in KZ by (clear - ArR; lia); zify_cond KZ; [exfalso; clear - KZ ArR; lia| clear KZ].

    step. step. if_cases K8; rewrite ?unsigned_lit in K8 by (clear - AL512; lia); zify_cond K8.
    {
      assert (E8 : al = 8%nat) by (clear - K8; lia). clear K8.
      replace (al =? 4)%nat with false by (rewrite E8; reflexivity). replace (al =? 8)%nat with true by (rewrite E8; reflexivity).
      ihere. to_implM. cbn [tbind fst snd]. rewrite sqr_model_fin by exact HVR4. rewrite <- EA4. rewrite E8 in *.
      eapply sqr_path_comba8; [exact ENV4 | exact LS4 | exact CEIL | exact GLO' | exact LO | exact SPB | exact B63 | exact FROK | exact HR4 | exact HP | exact HX4 | exact NX
        | intros E; apply NRX; symmetry; exact E | exact HPC | exact ALT | exact HDM]. }
    assert (N8 : al <> 8%nat) by (clear - K8; lia). clear K8.
    replace (al =? 8)%nat with false by (symmetry; apply Nat.eqb_neq; exact N8).
    step. step. if_cases K4; rewrite ?unsigned_lit in K4 by (clear - AL512; lia); zify_cond K4.
    2:{
      assert (E4 : al = 4%nat) by (clear - K4; lia). clear K4.
      replace (al =? 4)%nat with true by (rewrite E4; reflexivity).
      ihere. to_implM. cbn [tbind fst snd]. rewrite sqr_model_fin by exact HVR4. rewrite <- EA4. rewrite E4 in *.
      eapply sqr_path_comba4; [exact ENV4 | exact LS4 | exact CEIL | exact GLO' | exact LO | exact SPB | exact B63 | exact FROK | exact HR4 | exact HP | exact HX4 | exact NX
        | intros E; apply NRX; symmetry; exact E | exact HPC | exact ALT | exact HDM]. }
    assert (N4 : al <> 4%nat) by (clear - K4; lia). clear K4.
    replace (al =? 4)%nat with false by (symmetry; apply Nat.eqb_neq; exact N4).
    step. step. if_cases K16; rewrite ?unsigned_lit in K16 by (clear - AL512; lia); zify_cond K16.
    2:{
      assert (L16 : (al < 16)%nat) by (clear - K16; lia). clear K16.
      replace (al <? 16)%nat with true by (symmetry; apply Nat.ltb_lt; exact L16).
      ihere. to_implM. cbn [tbind fst snd]. rewrite sqr_model_fin by exact HVR4. rewrite <- EA4.
      eapply sqr_path_stack; [exact ENV4 | exact LS4 | exact CEIL | exact GLO' | exact LO | exact SPB | exact B63 | exact FROK | exact HR4 | exact HP | exact HX4 | exact NX
        | intros E; apply NRX; symmetry; exact E | exact HPC | split; [clear - ALP; lia| exact ALT] | exact L16 | exact HDM | exact SP16]. }
    assert (G16 : (16 <= al)%nat) by (clear - K16; lia). clear K16.
    replace (al <? 16)%nat with false by (symmetry; apply Nat.ltb_ge; exact G16).

    set (nb := num_bits_word (Z.of_nat al)) in *.
    assert (NBR : 5 <= nb <= 10).
    { unfold nb, num_bits_word. replace (Z.of_nat al =? 0) with false by (symmetry; apply Z.eqb_neq; clear - G16; lia).
      pose proof (Z.log2_le_mono 16 (Z.of_nat al) ltac:(clear - G16; lia)) as L1. pose proof (Z.log2_le_mono (Z.of_nat al) 512 AL512) as L2.
      change (Z.log2 16) with 4 in L1. change (Z.log2 512) with 9 in L2. clear - L1 L2. lia. }
    set (kj := Z.to_nat (nb - 1)) in *.
    assert (EKJ : Z.of_nat kj = nb - 1) by (unfold kj; clear - NBR; lia).
    assert (KJR : (4 <= kj <= 9)%nat) by (clear - EKJ NBR; lia).
    pose proof ENV4 as (HEAP4 & AUX4 & ST4 & (errv4 & ERR4) & MI4 & _ & _ & _ & _ & FR4 & FSZ4).
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS4) as PARTS4.
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -336)) = bv_unsigned sp + -336) by (apply unsigned_lit; lia).
    step. step.
    eapply evt_cut.
    { eapply (WU_num_bits_word.BN_num_bits_word_uspec) with (lo := lo); [rewrite ESP; exact ST4 | rewrite ESP; clear - LO'; lia | exact MI4]. }
    intros ms' PO. unfold WU_num_bits_word.nbw_upost in PO.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m5 & E & MUc & WMc & MIc & STc).
    subst ms'. rewrite ESP in *. rewrite (unsigned_lit (Z.of_nat al)) by (clear - AL512; lia). fold nb.
    lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?r)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 r)) with (Z_to_bv 64 r) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.
    assert (HWL5 : Forall (w_lib bs3 OW4 PL lo (bv_unsigned sp)) [(bv_unsigned sp + -336 - 16, bv_unsigned sp + -336)]) by (constructor; [left; cbn; clear - LO'; lia| constructor]).
    assert (WOK5 : Forall (w_ok OW4 LB bs3 PL EA (bv_unsigned sp) []) [(bv_unsigned sp + -336 - 16, bv_unsigned sp + -336)]) by (constructor; [apply w_stack; cbn; clear - LO' CEIL; lia| constructor]).
    pose proof (lib_state_frame st3 LB _ _ [] bs3 m4 m5 OW4 PL EA _ HEAP4 LS4 MUc WMc FROK WOK5) as LS5.
    lazymatch type of ENV4 with kenv _ _ _ _ _ _ _ _ _ _ ?fr _ _ _ _ =>
      assert (ENV5 : kenv LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -336) s bs OW m fr st3 bs3 m5 OW4) end.
    { eapply (kenv_silent LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -336) s bs OW m CEIL GLO' FBlo FBsp SPB FROK) with (errv' := errv4);
        [exact ENV4 | exact PARTS4 | exact MUc | exact WMc | exact HWL5 | exact STc | | exact MIc | | exact FSZ4].
      - eapply rw_cells_transport; [exact ERR4 | exact MUc | exact WMc |]. unfold LX_ERRNO, RATP. cbn. clear - GLO LO'. lia.
      - eapply rw_cells_transport; [exact FR4 | exact MUc | exact WMc |]. cbn. clear. lia. }
    clear ENV4 LS4 HEAP4 AUX4 ST4 ERR4 MI4 FR4 FSZ4 PARTS4 MUc WMc MIc STc HWL5 WOK5.
    assert (HC : nb = 5 \/ nb = 6 \/ nb = 7 \/ nb = 8 \/ nb = 9 \/ nb = 10) by (clear - NBR; lia).
    assert (EJ1 : Z_to_bv 64 (bv_swrap 32 (Z.shiftl 1 (bv_unsigned (Z_to_bv 64 (nb + -1)) mod 32))) = Z_to_bv 64 (Z.of_nat (2 ^ kj))).
    { unfold kj. clear - HC. destruct HC as [E|[E|[E|[E|[E|E]]]]]; rewrite E; reflexivity. }
    assert (J512 : (16 <= 2 ^ kj <= 512)%nat).
    { unfold kj. clear - HC. destruct HC as [E|[E|[E|[E|[E|E]]]]]; rewrite E; [change (16 <= 16 <= 512)%nat | change (16 <= 32 <= 512)%nat | change (16 <= 64 <= 512)%nat | change (16 <= 128 <= 512)%nat | change (16 <= 256 <= 512)%nat | change (16 <= 512 <= 512)%nat]; clear; lia. }
    clear HC.
    step. ub1 ub_kind.
    step. ub1 ub_kind. step. step. rewrite EJ1. step. step. ub1 ub_kind.
    step. if_cases KJ; rewrite ?unsigned_lit in KJ by (clear - AL512 J512; lia); zify_cond KJ.
    2:{
      assert (EJ : al = (2 ^ kj)%nat) by (clear - KJ; lia). clear KJ.
      replace (al =? 2 ^ kj)%nat with true by (symmetry; apply Nat.eqb_eq; exact EJ).
      step. step. ub1 ub_kind. step. setreg 11%Z (Z_to_bv 64 (Z.of_nat (4 * 2 ^ kj))) ltac:(f_equal; rewrite unsigned_lit by (clear - J512; lia); rewrite Z.shiftl_mul_pow2 by lia; rewrite bn_swrap32_small by (clear - J512; lia); lia).
      step.
      pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS5 HT4) as HVT4.
      pose proof (st_wf_ok t bs3 (proj1 (lib_state_h_parts _ _ _ _ _ _ LS5)) HVT4 (proj1 HPT)) as (_ & TDT & _).
      destruct (KPRE _ _ _ _ _ BN_WEXPAND_STACK ENV5 LS5 LOF) as (errv5 & PRE5).
      step.
      ihere. to_implM.
      apply BnAssoc.implM_embed_assoc. apply BnAssoc.implM_embed_assoc.
      eapply implM_embed_bind.
      { eapply BnLeaves.implM_embed_leaves; [apply (bn_wexpand_leaves2 t (4 * 2 ^ kj) bs3 HVT4 TDT)|].
        eapply (bn_wexpand_walk HM HF) with (r := t) (a := at_) (words := (4 * 2 ^ kj)%nat);
          [exact PRE5 | reflexivity | exact HT4 | exact (hpl_wref PL t HPT) | reflexivity | reflexivity | clear - J512; lia]. }
      cbv beta. intros [u5 bs4] st4 ms4 [PO LF4]. apply BPK in PO; [|intros v9 b9 o9 p9 a9 [E _]; exact E].
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m6 & OW6 & -> & KP & (_ & -> & HDT & WRES5 & BST5)).
      destruct (KPOST _ _ _ _ _ _ _ _ _ ENV5 KP) as (ENV6 & LS6). pose proof KP as RS6; apply kpost_refs in RS6.
      cbn [fst snd] in *. clear PRE5 KP ENV5 LS5.
      replace (ret_pc (Z_to_bv 64 1078560)) with (Z_to_bv 64 1078560) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      destruct LF4 as (LV1 & _). cbn [fst snd] in *. unfold MallocRep.wz.
      pose proof (ref_at_stable _ _ _ _ PL _ _ RS6 HR4) as HR6. pose proof (ref_at_stable _ _ _ _ PL _ _ RS6 HX4) as HX6. pose proof (ref_at_stable _ _ _ _ PL _ _ RS6 HT4) as HT6.
      assert (EA6 : getbn rx bs4 = a) by (rewrite LV1 by (intros E; apply NXT; symmetry; exact E); exact EA4).
      assert (ER6 : getbn rr bs4 = getbn rr bs3) by (apply LV1; exact NTR).
      pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS6 HR6) as HVR6.
      unfold implM. iprefix.
      step. if_cases KZ; rewrite ?unsigned_lit in KZ by (clear - AtR; lia); zify_cond KZ; [exfalso; clear - KZ AtR; lia| clear KZ].
      ihere. to_implM.
      rewrite <- EA6. rewrite EJ in *.
      set (X := sqr_recursive kj (firstn (2 ^ kj) (bn_buf (getbn rx bs4))) (firstn (2 * 2 ^ kj) (bn_buf (getbn rr bs4))) (bn_buf (getbn t bs4))).
      assert (EX : X = (fst X, snd X)) by (destruct X; reflexivity). rewrite EX. cbn [tbind fst snd].
      rewrite sqr_model_fin by (rewrite length_setbn; exact HVR6). subst X.
      eapply sqr_path_rec; [exact ENV6 | exact LS6 | exact CEIL | exact GLO' | exact LO | exact SPB | exact B63 | exact FROK | exact HR6 | exact HP | exact HX6 | exact NX
        | intros E; apply NRX; symmetry; exact E | exact HT6 | exact HPT | exact NTR | exact NXT | exact HPC
        | clear - KJR; lia | rewrite EA6; fold al; rewrite EJ; apply Nat.le_refl | rewrite ER6; exact HDM
        | pose proof (sqr_scratch_le kj) as SL; clear - SL HDT; lia ]. }

    assert (NJ : al <> (2 ^ kj)%nat) by (clear - KJ; lia). clear KJ.
    replace (al =? 2 ^ kj)%nat with false by (symmetry; apply Nat.eqb_neq; exact NJ).
    step. step.
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS5 HT4) as HVT4.
    pose proof (st_wf_ok t bs3 (proj1 (lib_state_h_parts _ _ _ _ _ _ LS5)) HVT4 (proj1 HPT)) as (_ & TDT & _).
    destruct (KPRE _ _ _ _ _ BN_WEXPAND_STACK ENV5 LS5 LOF) as (errv5 & PRE5).
    step.
    ihere. to_implM.
    apply BnAssoc.implM_embed_assoc. apply BnAssoc.implM_embed_assoc.
    eapply implM_embed_bind.
    { eapply BnLeaves.implM_embed_leaves; [apply (bn_wexpand_leaves2 t (2 * al) bs3 HVT4 TDT)|].
      eapply (bn_wexpand_walk HM HF) with (r := t) (a := at_) (words := (2 * al)%nat);
        [exact PRE5 | reflexivity | exact HT4 | exact (hpl_wref PL t HPT) | reflexivity | reflexivity | clear - AL512; lia]. }
    cbv beta. intros [u5 bs4] st4 ms4 [PO LF4]. apply BPK in PO; [|intros v9 b9 o9 p9 a9 [E _]; exact E].
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m6 & OW6 & -> & KP & (_ & -> & HDT & WRES5 & BST5)).
    destruct (KPOST _ _ _ _ _ _ _ _ _ ENV5 KP) as (ENV6 & LS6). pose proof KP as RS6; apply kpost_refs in RS6.
    cbn [fst snd] in *. clear PRE5 KP ENV5 LS5.
    replace (ret_pc (Z_to_bv 64 1078612)) with (Z_to_bv 64 1078612) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    destruct LF4 as (LV1 & _). cbn [fst snd] in *. unfold MallocRep.wz.
    pose proof (ref_at_stable _ _ _ _ PL _ _ RS6 HR4) as HR6. pose proof (ref_at_stable _ _ _ _ PL _ _ RS6 HX4) as HX6. pose proof (ref_at_stable _ _ _ _ PL _ _ RS6 HT4) as HT6.
    assert (EA6 : getbn rx bs4 = a) by (rewrite LV1 by (intros E; apply NXT; symmetry; exact E); exact EA4).
    assert (ER6 : getbn rr bs4 = getbn rr bs3) by (apply LV1; exact NTR).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS6 HR6) as HVR6.
    unfold implM. iprefix.
    step. if_cases KZ; rewrite ?unsigned_lit in KZ by (clear - AtR; lia); zify_cond KZ; [exfalso; clear - KZ AtR; lia| clear KZ].
    ihere. to_implM.
    rewrite <- EA6.
    set (X := sqr_normal (firstn al (bn_buf (getbn rx bs4))) (firstn (2 * al) (bn_buf (getbn rr bs4)))).
    assert (EX : X = (fst X, sqr_words (firstn al (bn_buf (getbn rx bs4))))) by reflexivity. rewrite EX. cbn [tbind fst snd].
    rewrite sqr_model_fin by (rewrite length_setbn; exact HVR6). subst X.
    eapply sqr_path_ntmp; [exact ENV6 | exact LS6 | exact CEIL | exact GLO' | exact LO | exact SPB | exact B63 | exact FROK | exact HR6 | exact HP | exact HX6 | exact NX
      | intros E; apply NRX; symmetry; exact E | exact HT6 | exact HPT | exact NTR | exact NXT | exact HPC
      | split; [clear - ALP; lia| rewrite EA6; fold al; apply Nat.le_refl] | rewrite ER6; exact HDM | exact HDT ].
  Qed.

  Lemma BN_sqr_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (rr rx : bnref) (ar ax ac : Z) (qc : bptr),
    bn_pre s bs m OW LB PL EA sp lo B errv BN_SQR_STACK -> tp = wz RATP -> bv_unsigned sp mod 16 = 0 ->
    ref_at bs OW PL rr ar -> ref_at bs OW PL rx ax -> hpl PL rr -> rx <> ROne -> pl_ctx PL = Some (ac, qc) ->
    a0 = wz ar -> a1 = wz ax -> a2 = wz ac ->
    implM bgusegs (interp (embed (BN_sqr (tree_ops bptr) rr rx bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_SQR) fc None m (seg_rom bgusegs)).
  Proof.
    intros until qc. intros (HEAP & LS & FROK & AUX & SPB & B63 & ST & CEIL & GLO & LO & ERR & MI) -> SP16 HR HX HP NX HPC -> -> ->.
    unfold BN_SQR_STACK, BN_SQR, GLOBALS_TOP, MallocRep.wz in *. pose proof LO as LO'. unfold BN_SQR_FIXED_STACK, BN_WEXPAND_STACK, BN_EXPAND2_STACK in LO'.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgusegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3346328 - 164) with 3346164 in ERR.
    assert (GLO' : GLOBALS_TOP <= lo) by exact GLO.
    unfold BN_sqr, bbind. cbn [bind tree_ops tbind fst snd].
    unfold implM. iprefix.
    carve_frame 32%nat ST. do 6 step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HWL : Forall (w_lib bs OW PL lo (bv_unsigned sp)) [(bv_unsigned sp + -32, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
    assert (WOK : Forall (w_ok OW LB bs PL EA (bv_unsigned sp) []) [(bv_unsigned sp + -32, bv_unsigned sp)]) by (constructor; [apply w_stack; cbn; lia| constructor]).
    pose proof (lib_state_frame s LB _ _ [] bs m m1 OW PL EA _ HEAP LS MU WM FROK WOK) as LS1.
    lazymatch type of FR with rw_cells _ _ _ ?fr =>
      assert (ENV : kenv LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -32) s bs OW m fr s bs m1 OW)
    end.
    { unfold kenv. split; [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL)|].
      split; [apply (seg_auxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK AUX MU WM HWL SPB ltac:(lia)); exact GLO'|].
      split; [exact ST|]. split; [exists errv; unfold LX_ERRNO, RATP; exact ERR|]. split; [exact MI|].
      split; [apply (seg_lx_pres _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL); lia|].
      split; [reflexivity|]. split; [reflexivity|]. split; [apply refs_stable_refl|]. split; [exact FR| cbn; lia]. }
    assert (FBlo : lo <= bv_unsigned sp + -32) by lia.
    assert (FBsp : bv_unsigned sp + -32 <= bv_unsigned sp) by lia.
    assert (SPR2 : bv_unsigned sp < 2 ^ 64) by lia.
    pose proof (kenv_pre LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -32) s bs OW m CEIL GLO' FBlo FBsp SPB B63 SPR2 FROK) as KPRE.
    pose proof (kenv_post LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -32) s bs OW m CEIL GLO' FBlo FBsp FROK) as KPOST.
    pose proof (fun A => @bn_post_kpost _ _ LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -32) CEIL FBlo FBsp SPR2 A) as BPK.
    assert (LOF : lo <= bv_unsigned sp + -32 - BN_SQR_FIXED_STACK) by lia.
    clear HEAP AUX ST ERR MI MU WM HWL WOK FR.
    destruct (KPRE _ _ _ _ _ BN_SQR_FIXED_STACK ENV LS1 LOF) as (errv1 & PRE1).
    step.
    ihere. to_implM.
    eapply implM_embed_bind.
    { eapply bn_sqr_fixed_top_walk with (rr := rr) (rx := rx); [exact PRE1 | reflexivity | rewrite unsigned_lit by lia; clear - SP16; Z.div_mod_to_equations; lia
        | exact HR | exact HX | exact HP | exact NX | exact HPC | reflexivity | reflexivity | reflexivity]. }
    cbv beta. intros [u1 bs1] st1 ms1 PO. apply BPK in PO; [|intros v9 b9 o9 p9 a9 [E _]; exact E].
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & OW2 & -> & KP & (_ & ->)).
    destruct (KPOST _ _ _ _ _ _ _ _ _ ENV KP) as (ENV2 & LS2). pose proof KP as RS2; apply kpost_refs in RS2.
    cbn [fst snd] in *. clear PRE1 KP ENV LS1.
    replace (ret_pc (Z_to_bv 64 1078164)) with (Z_to_bv 64 1078164) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (ref_at_stable _ _ _ _ PL _ _ RS2 HR) as HR2.
    unfold bbind, bget, bset. cbn [bind ret tree_ops tbind fst snd embed interp]. apply implM_interp_ret.
    step. step. step.
    eapply (ctop_call LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -32) s bs OW m CEIL GLO' FBlo FBsp SPB B63 SPR2 FROK);
      [clear - LOF; unfold BN_SQR_FIXED_STACK, BN_WEXPAND_STACK, BN_EXPAND2_STACK in LOF; lia | exact ENV2 | exact LS2 | exact HR2 | exact (hpl_wref PL rr HP) |].
    intros m3 z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 ENV3 LS3.
    replace (ret_pc (Z_to_bv 64 1078176)) with (Z_to_bv 64 1078176) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (kenv_final LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -32) s bs OW m _ _ _ _ _ ENV3) as (F1 & F2 & STF & (errvF & F4) & F5 & F6 & F7 & F8 & F9 & FRF).
    step. do 4 step. release_frame FRF STF (bv_unsigned sp). step. step.
    apply evt_done. unfold bn_post. do 15 eexists. exists m3, OW2, PL, errvF. split; [reflexivity|]. cbn [fst snd].
    split; [exact F1|]. split; [exact LS3|]. split; [exact F2|]. split; [exact STF|]. split; [exact F4|]. split; [exact F5|].
    split; [exact F6|]. split; [exact F7|]. split; [exact F8|]. split; [exact F9|]. split; reflexivity.
  Qed.

  Lemma bn_pre_mono : forall s bs m OW LB PL EA sp lo B errv K K',
    bn_pre s bs m OW LB PL EA sp lo B errv K' -> K <= K' -> bn_pre s bs m OW LB PL EA sp lo B errv K.
  Proof.
    intros s bs m OW LB PL EA sp lo B errv K K' (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12) HK.
    unfold bn_pre. repeat (split; [assumption|]). split; [clear - H10 HK; lia|]. split; assumption.
  Qed.

  Lemma bn_sqr_fixed_top_walk_cs : forall (CS : Z), BN_SQR_FIXED_STACK <= CS -> forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (rr rx : bnref) (ar ax ac : Z) (qc : bptr),
    bn_pre s bs m OW LB PL EA sp lo B errv CS -> tp = wz RATP -> bv_unsigned sp mod 16 = 0 ->
    ref_at bs OW PL rr ar -> ref_at bs OW PL rx ax -> hpl PL rr -> rx <> ROne -> pl_ctx PL = Some (ac, qc) ->
    a0 = wz ar -> a1 = wz ax -> a2 = wz ac ->
    implM bgusegs (interp (embed (bn_sqr_fixed_top (tree_ops bptr) rr rx bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_SQR_FIXED_TOP) fc None m (seg_rom bgusegs)).
  Proof. intros CS HCS. intros until qc. intros PRE. eapply bn_sqr_fixed_top_walk. exact (bn_pre_mono _ _ _ _ _ _ _ _ _ _ _ _ _ PRE HCS). Qed.

End Proofs.
End WithCeiling0.
