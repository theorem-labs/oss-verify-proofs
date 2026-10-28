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
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require Import BnHeap W_small W_small2.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require BnRep BnLeaves.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgRepU Require Import BgRepDefs BgRep BgLayer BgIface BnUAlign.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnA Require Import BnAPure.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnAU Require Import BnAKit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnRU Require Import W_expand BnCall BnRKit W_cmp W_uadd W_usub.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition BN_ADD : Z := 0x10a744.
Definition BN_ADD_STACK : Z := 48 + BN_UADD_STACK.

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Lemma add_fin : forall
      (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BgBnU.BnRep.err_addrs) (lo B : Z)
      (st : PState) (lsx : bstate bptr) (mx : mem) (OWx : list block) (rneg : bool) (rr : bnref) (R : Z)
      (x1 t0 t1 t2 x8 a1 a2 a3 a4 a5 a6 a7 x18 x19 t3 t4 t5 t6 : word),
    cenv LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -48) s bs OW m [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] st lsx mx OWx ->
    lib_state lsx mx OWx PL EA ->
    alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - 48 -> bv_unsigned sp <= B -> frames_ok PL (bv_unsigned sp) B ->
    ref_at lsx OWx PL rr R -> hpl PL rr ->
    evt bgusegs (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1)
                       (tt, setbn rr (bn_with_neg (getbn rr lsx) rneg) lsx) st)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp (wz RATP) t0 t1 t2 x8 (Z_to_bv 64 R) (wz 1) a1 a2 a3 a4 a5 a6 a7
               x18 x19 (Z_to_bv 64 (Z.b2z rneg)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x10a7f0) fc None mx (seg_rom bgusegs)).
  Proof.
    intros until t6. intros ENV LS CEIL GLO LO SPB FROK HR HP. pose proof (proj1 HP) as NRO.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof ENV as (HEAP & AUX & ST & (errv & ERR) & MI & LXP & FA & SO & RS & FR & _).
    unfold LX_ERRNO, RATP in ERR. change (3346328 - 164) with 3346164 in ERR.
    pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
    destruct (lib_state_open [] lsx mx OWx PL EA rr R LS ND HR ltac:(intros []) NRO) as ((Dr & SR & ARR) & OKR & LSH).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HR) as HVR.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS; pose proof PARTS as (WFS & PWF & IDS & PLB & ERRB).
    destruct (bn_arr_facts_w lsx OWx PL EA (bv_unsigned sp) B st LB mx rr Dr HEAP PARTS FROK HVR (hpl_wref PL rr HP) ARR) as (U & LENW & D0 & DC & DI & DSEP).
    specialize (DSEP rr R HR).
    pose proof (ref_at_hrange _ _ _ _ _ _ _ _ _ HEAP PARTS HR HP) as (SA0 & SAC & SAI & (qs & As & ns & Hins & Ra1 & Ra2)).
    set (b := getbn rr lsx) in *.
    unfold bn_cells, MallocRep.wz in SR. unfold GLOBALS_TOP in GLO.
    pose proof (munch_refl [(R, R + 24)]%Z mx) as MU. pose proof (wmono_refl bgusegs mx) as WM.
    zstep. rewrite (land7 R (proj2 (ref_at_ualign st OWx LB mx lsx PL EA rr R HEAP PARTS HR NRO))). chk_lit.
    zstep.
    do 6 zstep. release_frame FR ST (bv_unsigned sp). zstep. zstep.
    apply evt_done.
    lazymatch goal with |- bn_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (MS _ _ _ _ _ ?mf _) => rename mf into mF end.
    assert (HWL : Forall (w_lib lsx OWx PL lo (bv_unsigned sp)) [(R, R + 24)]).
    { constructor; [right; left; exists (qs, As, ns); cbn [blk_addr blk_size fst snd]; split; [exact Hins | lia] | constructor]. }
    assert (WOK : Forall (w_ok OWx LB lsx PL EA (bv_unsigned sp) [rr]) [(R, R + 24)]).
    { constructor; [eapply (w_struct OWx LB lsx PL EA (bv_unsigned sp) false [rr] _ rr R); [left; reflexivity | exact HR | exact NRO | cbn; lia | cbn; lia] | constructor]. }
    unfold bn_post. do 15 eexists. exists mF, OWx, PL, errv. split; [reflexivity|]. cbn [fst snd].
    split; [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL)|].
    split.
    { unfold lib_state. eapply (lib_state_close [] lsx mF OWx PL EA rr R); [| exact ND | exact HR | exact NRO | | |].
      - eapply (lib_state_frame st LB (bv_unsigned sp) B); [exact HEAP| exact LSH| exact MU| exact WM| exact FROK| exact WOK].
      - exists Dr. split; [unfold bn_cells, bn_with_neg, bn_dmax; cbn [bn_top bn_buf bn_neg bn_flags]; exact SR|].
        eapply bn_arr_of_u64arr; [exact ARR | exact U].
      - destruct OKR as (O1 & O2 & O3 & O4). unfold bg_ok, bn_with_neg, bn_dmax in *. cbn [bn_top bn_buf bn_flags]. auto.
      - apply ids_ok_setbn_same; [exact IDS | exact HVR | reflexivity]. }
    split; [apply (seg_auxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK AUX MU WM HWL SPB ltac:(lia)); unfold GLOBALS_TOP; lia|].
    split; [exact ST|]. split; [unfold LX_ERRNO, RATP; exact ERR|]. split; [exact MI|].
    split. { eapply lx_pres_trans; [exact LXP|]. apply (seg_lx_pres _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL); [unfold GLOBALS_TOP; lia | lia]. }
    split; [exact FA|]. split; [exact SO|].
    split. { eapply refs_stable_trans; [exact RS| apply refs_stable_setbn]. }
    split; reflexivity.
  Qed.

  Definition add_join (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BgBnU.BnRep.err_addrs) (lo B : Z) (rr : bnref) (R : Z)
      (v : bool * bstate bptr) (st' : PState) : machine_state -> Prop :=
    fun ms' => exists x1 t0 t1 t2 x8 a1 a2 a3 a4 a5 a6 a7 x18 x19 t3 t4 t5 t6 m' OW',
      ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp (wz RATP) t0 t1 t2 x8 (Z_to_bv 64 R) (wz 1) a1 a2 a3 a4 a5 a6 a7
                    x18 x19 (Z_to_bv 64 (Z.b2z (fst v))) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x10a7f0) fc None m' (seg_rom bgusegs)
      /\ cenv LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -48) s bs OW m [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] st' (snd v) m' OW'
      /\ lib_state (snd v) m' OW' PL EA /\ ref_at (snd v) OW' PL rr R.

  Lemma add_usub_path : forall
      (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BgBnU.BnRep.err_addrs) (lo B : Z)
      (st : PState) (lsx : bstate bptr) (mx : mem) (OWx : list block) (n : bool) (rr p q : bnref) (R P Q : Z)
      (x1 t0 t1 t2 x8 a3 a4 a5 a6 a7 x18 x19 t3 t4 t5 t6 : word),
    cenv LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -48) s bs OW m [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] st lsx mx OWx ->
    lib_state lsx mx OWx PL EA ->
    alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - BN_ADD_STACK -> bv_unsigned sp <= B -> frames_ok PL (bv_unsigned sp) B ->
    ref_at lsx OWx PL rr R -> hpl PL rr -> ref_at lsx OWx PL p P -> p <> ROne -> ref_at lsx OWx PL q Q -> q <> ROne ->
    implM bgusegs (interp (embed (tbind (BN_usub (tree_ops bptr) rr p q lsx) (fun p0 : unit * bstate bptr => TRet (n, snd p0))))) st
      (add_join ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s bs OW LB PL EA lo B rr R)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp (wz RATP) t0 t1 t2 x8 (Z_to_bv 64 R) (Z_to_bv 64 R) (Z_to_bv 64 P) (Z_to_bv 64 Q)
               a3 a4 a5 a6 a7 x18 x19 (Z_to_bv 64 (Z.b2z n)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x10a7cc) fc None mx (seg_rom bgusegs)).
  Proof.
    intros until t6. intros ENV LS CEIL GLO LO SPB FROK HR HPL HP NP HQ NQ.
    destruct (ref_at_hrange _ _ _ _ _ _ _ _ _ (proj1 ENV) (lib_state_h_parts _ _ _ _ _ _ LS) HR HPL) as (R0 & RC & _).
    unfold BN_ADD_STACK, BN_UADD_STACK, BN_WEXPAND_STACK, BN_EXPAND2_STACK in LO.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (FBlo : lo <= bv_unsigned sp + -48) by lia.
    assert (FBsp : bv_unsigned sp + -48 <= bv_unsigned sp) by lia.
    assert (SPR2 : bv_unsigned sp < 2 ^ 64) by lia.
    pose proof (cenv_pre LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -48) s bs OW m CEIL GLO FBlo FBsp SPB SPR2 FROK) as CPRE.
    pose proof (cenv_post LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -48) s bs OW m CEIL GLO FBlo FBsp FROK) as CPOST.
    pose proof (fun A => @bn_post_cpost _ _ LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -48) CEIL FBlo FBsp SPR2 A) as BPC.
    unfold implM. iprefix. zstep.
    destruct (CPRE _ _ _ _ _ BN_USUB_STACK ENV LS ltac:(unfold BN_USUB_STACK, BN_WEXPAND_STACK, BN_EXPAND2_STACK; lia)) as (errv1 & PRE1).
    ihere. to_implM.
    eapply implM_embed_bind.
    { eapply (BN_usub_walk HM HF) with (lo := lo) (B := B) (errv := errv1) (OW := OWx) (LB := LB) (PL := PL) (EA := EA)
        (rr := rr) (x := p) (y := q) (R := R) (X := P) (Y := Q);
        [exact PRE1 | reflexivity | exact HR | exact HPL | exact HP | exact NP | exact HQ | exact NQ | reflexivity | reflexivity | reflexivity]. }
    cbv beta. intros [[] lsu] stu msu PO. apply BPC in PO. cbn [fst snd] in PO.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m2 & OW1 & PL1 & -> & CP & (EPL & -> & _)).
    subst PL1. specialize (CP eq_refl).
    destruct (CPOST _ _ _ _ _ _ _ _ _ ENV CP) as (ENV1 & LS1).
    pose proof (cpost_refs LB PL EA lo B (bv_unsigned sp + -48) _ _ _ _ _ _ _ _ CP) as RS.
    replace (ret_pc (Z_to_bv 64 1091536)) with (Z_to_bv 64 1091536) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    cbn [embed interp fst snd]. apply implM_interp_ret.
    chk ltac:(fun C => clear - C R0 RC; lia).
    zstep. apply evt_done.
    unfold add_join. do 18 eexists. exists m2, OW1. split; [reflexivity|]. cbn [fst snd].
    split; [exact ENV1|]. split; [exact LS1 | exact (ref_at_stable _ _ _ _ _ _ _ RS HR)].
  Qed.

  Lemma BN_add_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BgBnU.BnRep.err_addrs)
      (lo B : Z) (errv : word) (rr x y : bnref) (R X Y : Z),
    bn_pre s bs m OW LB PL EA sp lo B errv BN_ADD_STACK -> tp = wz RATP ->
    ref_at bs OW PL rr R -> hpl PL rr -> ref_at bs OW PL x X -> x <> ROne -> ref_at bs OW PL y Y -> y <> ROne ->
    a0 = wz R -> a1 = wz X -> a2 = wz Y ->
    implM bgusegs (interp (embed (BN_add (tree_ops bptr) rr x y bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_ADD) fc None m (seg_rom bgusegs)).
  Proof.
    intros until Y. intros PRE -> HR HPL HX NX HY NY -> -> ->. pose proof (proj1 HPL) as NRO.
    pose proof PRE as (HEAP & LS & FROK & AUX & SPB & B63 & ST & CEIL & GLO & LO & ERR & MI).
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
    unfold BN_ADD_STACK, BN_UADD_STACK, BN_WEXPAND_STACK, BN_EXPAND2_STACK in LO.
    unfold BN_ADD, MallocRep.wz.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    destruct (open_ro_u s OW LB m bs PL EA (bv_unsigned sp) B x X HEAP LS FROK HX NX) as (Dx0 & SX & OKX & _ & X0 & XC & _ & _ & ALX0 & _).
    destruct (open_ro_u s OW LB m bs PL EA (bv_unsigned sp) B y Y HEAP LS FROK HY NY) as (Dy0 & SY & OKY & _ & Y0 & YC & _ & _ & ALY0 & _).
    destruct (ref_at_hrange _ _ _ _ _ _ _ _ _ HEAP PARTS HR HPL) as (R0 & RC & _).
    unfold bn_cells, MallocRep.wz in SX, SY.
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgusegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3346328 - 164) with 3346164 in ERR.
    assert (GLO' : GLOBALS_TOP <= lo) by exact GLO. unfold GLOBALS_TOP in GLO.
    unfold BN_add, bbind, bget, bset, bret. cbn [bind ret tree_ops tbind fst snd].
    set (na := bn_neg (getbn x bs)) in *. set (nb := bn_neg (getbn y bs)) in *.
    assert (NA : 0 <= Z.b2z na <= 1) by (destruct na; cbn; lia).
    assert (NB : 0 <= Z.b2z nb <= 1) by (destruct nb; cbn; lia).
    unfold implM. iprefix.
    carve_frame 48%nat ST. do 8 zstep.
    chk ltac:(fun C => clear - C X0 XC; lia).
    do 3 zstep. rewrite (land7 X (hide_elim _ ALX0)). chk_lit.
    zstep.
    chk ltac:(fun C => clear - C Y0 YC; lia).
    zstep. rewrite (land7 Y (hide_elim _ ALY0)). chk_lit.
    zstep. rewrite (sx32_small (Z.b2z na)) by (clear - NA; lia).
    zstep. rewrite (sx32_small (Z.b2z nb)) by (clear - NB; lia).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HWL0 : Forall (w_lib bs OW PL lo (bv_unsigned sp)) [(bv_unsigned sp + -48, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
    assert (WOK0 : Forall (w_ok OW LB bs PL EA (bv_unsigned sp) []) [(bv_unsigned sp + -48, bv_unsigned sp)]) by (constructor; [apply w_stack; cbn; lia| constructor]).
    pose proof (lib_state_frame s LB _ _ [] bs m m1 OW PL EA _ HEAP LS MU WM FROK WOK0) as LS0.
    lazymatch type of FR with rw_cells _ _ _ ?fr =>
      assert (ENV : cenv LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -48) s bs OW m fr s bs m1 OW)
    end.
    { unfold cenv. split; [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL0 CEIL)|].
      split; [apply (seg_auxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK AUX MU WM HWL0 SPB ltac:(lia)); exact GLO'|].
      split; [exact ST|]. split; [exists errv; unfold LX_ERRNO, RATP; exact ERR|]. split; [exact MI|].
      split; [apply (seg_lx_pres _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL0 CEIL); [exact GLO'| lia]|].
      split; [reflexivity|]. split; [reflexivity|]. split; [apply refs_stable_refl|]. split; [exact FR| cbn; lia]. }
    assert (FBlo : lo <= bv_unsigned sp + -48) by lia.
    assert (FBsp : bv_unsigned sp + -48 <= bv_unsigned sp) by lia.
    assert (SPR2 : bv_unsigned sp < 2 ^ 64) by lia.
    pose proof (cenv_pre LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -48) s bs OW m CEIL GLO' FBlo FBsp SPB SPR2 FROK) as CPRE.
    pose proof (cenv_post LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -48) s bs OW m CEIL GLO' FBlo FBsp FROK) as CPOST.
    pose proof (fun A => @bn_post_cpost _ _ LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -48) CEIL FBlo FBsp SPR2 A) as BPC.
    assert (LOF : lo <= bv_unsigned sp - 48) by lia.
    clear HEAP LS AUX ST ERR MI MU WM HWL0 WOK0 FR PRE SX SY.
    zstep. if_cases K; zify_cond K.
    2:{
      replace (eqb na nb) with true by (symmetry; clear - K; destruct na, nb; cbn in *; congruence).
      do 4 zstep.
      destruct (CPRE _ _ _ _ _ BN_UADD_STACK ENV LS0 ltac:(unfold BN_UADD_STACK, BN_WEXPAND_STACK, BN_EXPAND2_STACK; lia)) as (errv1 & PRE1).
      ihere. to_implM.
      eapply implM_embed_bind with (Q1 := fun (v : bool * bstate bptr) st' ms' => fst v = na /\
          bn_post (Z_to_bv 64 1091492) (Z_to_bv 64 (bv_unsigned sp + -48)) gp sp (Z_to_bv 64 R) (Z_to_bv 64 Y) (Z_to_bv 64 X)
                  (Z_to_bv 64 (Z.b2z na)) s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m1 PL EA (uarith_res rr bs OW PL) (tt, snd v) st' ms').
      { eapply implM_embed_bind.
        { eapply (BN_uadd_walk HM HF) with (lo := lo) (B := B) (errv := errv1) (OW := OW) (LB := LB) (PL := PL) (EA := EA)
            (rr := rr) (ra_ := x) (rb_ := y) (R := R) (A := X) (Bb := Y);
            [exact PRE1 | reflexivity | exact HR | exact HPL | exact HX | exact NX | exact HY | exact NY | reflexivity | reflexivity | reflexivity]. }
        cbv beta. intros [[] lsu] stu msu PO. cbn [embed interp fst snd]. apply implM_interp_ret. apply evt_done.
        split; [reflexivity | exact PO]. }
      cbv beta. intros [rn lsu] stu msu [Ern PO]. cbn [fst snd] in *. subst rn. apply BPC in PO.
      destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m2 & OW1 & PL1 & -> & CP & (EPL & -> & _)).
      subst PL1. specialize (CP eq_refl).
      destruct (CPOST _ _ _ _ _ _ _ _ _ ENV CP) as (ENV1 & LS1).
      pose proof (cpost_refs LB PL EA lo B (bv_unsigned sp + -48) _ _ _ _ _ _ _ _ CP) as RS.
      cbn [fst snd] in *.
      replace (ret_pc (Z_to_bv 64 1091492)) with (Z_to_bv 64 1091492) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      cbn [embed interp]. apply implM_interp_ret.
      zstep. if_cases C; zify_cond C; [| exfalso; clear - C R0 RC; lia]. clear C.
      eapply add_fin; [exact ENV1 | exact LS1 | exact CEIL | exact GLO' | exact LOF | exact SPB | exact FROK | exact (ref_at_stable _ _ _ _ _ _ _ RS HR) | exact HPL]. }

    replace (eqb na nb) with false by (symmetry; clear - K; destruct na, nb; cbn in *; congruence).
    do 3 zstep.
    destruct (CPRE _ _ _ _ _ BN_UCMP_STACK ENV LS0 ltac:(unfold BN_UCMP_STACK; lia)) as (errv1 & PRE1).
    ihere. to_implM.
    eapply implM_embed_bind with (Q1 := add_join ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s bs OW LB PL EA lo B rr R).
    2:{ cbv beta. intros [rn lsu] stu msu (x1 & u0 & u1 & u2 & x8 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & x18 & x19 & u3 & u4 & u5 & u6 & m' & OW' & -> & ENV' & LS' & HR').
        cbn [fst snd] in *. cbn [embed interp]. apply implM_interp_ret.
        eapply add_fin; [exact ENV' | exact LS' | exact CEIL | exact GLO' | exact LOF | exact SPB | exact FROK | exact HR' | exact HPL]. }
    eapply implM_embed_bind.
    { eapply BN_ucmp_walk with (lo := lo) (B := B) (errv := errv1) (OW := OW) (LB := LB) (PL := PL) (EA := EA) (r1 := x) (r2 := y) (a := X) (b := Y);
        [exact PRE1 | reflexivity | exact HX | exact HY | exact NX | exact NY | reflexivity | reflexivity]. }
    cbv beta. intros [c lsc] stc msc PO. apply BPC in PO. cbn [fst snd] in PO.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m2 & OW1 & PL1 & -> & CP & ((EPL & -> & CR & -> & ->) & EC)).
    subst PL1. specialize (CP eq_refl).
    destruct (CPOST _ _ _ _ _ _ _ _ _ ENV CP) as (ENV1 & LS1).
    pose proof (cpost_refs LB PL EA lo B (bv_unsigned sp + -48) _ _ _ _ _ _ _ _ CP) as RS.
    cbn [fst snd] in *.
    replace (ret_pc (Z_to_bv 64 1091512)) with (Z_to_bv 64 1091512) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    clear PRE1 CP ENV LS0 EC.
    unfold implM. iprefix.
    pose proof ENV1 as (HEAP2 & _ & ST2 & _ & MI2 & _).
    pose proof (ref_at_stable _ _ _ _ _ _ _ RS HR) as HR1. pose proof (ref_at_stable _ _ _ _ _ _ _ RS HX) as HX1. pose proof (ref_at_stable _ _ _ _ _ _ _ RS HY) as HY1.
    destruct (open_ro stc OW LB m2 bs PL EA (bv_unsigned sp) B x X HEAP2 LS1 FROK HX1 NX) as (Dx1 & SX & _).
    destruct (open_ro stc OW LB m2 bs PL EA (bv_unsigned sp) B y Y HEAP2 LS1 FROK HY1 NY) as (Dy1 & SY & _).
    unfold bn_cells, MallocRep.wz in SX, SY. fold na in SX. fold nb in SY.
    zstep. if_cases K1; zify_cond K1.
    2:{
      assert (K1' : (0 <? c) = true) by (rewrite <- (land64_pos_iff c) by (clear - CR; lia); apply andb_true_iff; split; apply Z.ltb_lt; assumption).
      zstep. rewrite (sx32_small (Z.b2z na)) by (clear - NA; lia).
      do 3 zstep.
      ihere. to_implM. rewrite K1'.
      eapply add_usub_path; [exact ENV1 | exact LS1 | exact CEIL | exact GLO' | | exact SPB | exact FROK | exact HR1 | exact HPL | exact HX1 | exact NX | exact HY1 | exact NY].
      unfold BN_ADD_STACK, BN_UADD_STACK, BN_WEXPAND_STACK, BN_EXPAND2_STACK. lia. }
    rewrite land64_pos_iff in K1 by (clear - CR; lia).
    zstep. if_cases K2; zify_cond K2.
    {
      rewrite land64_neg_iff in K2 by (clear - CR; lia).
      assert (K2' : (c <? 0) = true) by (apply Z.ltb_lt; exact K2).
      zstep. rewrite (sx32_small (Z.b2z nb)) by (clear - NB; lia).
      do 4 zstep.
      ihere. to_implM. rewrite K1, K2'.
      eapply add_usub_path; [exact ENV1 | exact LS1 | exact CEIL | exact GLO' | | exact SPB | exact FROK | exact HR1 | exact HPL | exact HY1 | exact NY | exact HX1 | exact NX].
      unfold BN_ADD_STACK, BN_UADD_STACK, BN_WEXPAND_STACK, BN_EXPAND2_STACK. lia. }

    assert (K2' : (c <? 0) = false).
    { apply Z.ltb_ge. destruct (Z_lt_ge_dec c 0) as [Hc|Hc]; [|lia]. exfalso.
      apply (land64_neg_iff c ltac:(clear - CR; lia)) in Hc. clear - Hc K2. lia. }
    pose proof ENV1 as (_ & _ & _ & (errv2 & ERR2) & _ & _ & _ & _ & _ & FR2 & _).
    pose proof (RH_nodup_l _ _ _ _ HEAP2) as ND2.
    destruct (lib_state_open [] bs m2 OW PL EA rr R LS1 ND2 HR1 ltac:(intros []) NRO) as ((Dr & SR & ARR) & OKR & LSH).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS1 HR1) as HVR.
    clear PARTS. pose proof (lib_state_h_parts _ _ _ _ _ _ LS1) as PARTS; pose proof PARTS as (WFS & PWF & IDS & PLB & ERRB).
    destruct (bn_arr_facts_w bs OW PL EA (bv_unsigned sp) B stc LB m2 rr Dr HEAP2 PARTS FROK HVR (hpl_wref PL rr HPL) ARR) as (U & LENW & D0 & DC & DI & DSEP).
    specialize (DSEP rr R HR1).
    pose proof (ref_at_hrange _ _ _ _ _ _ _ _ _ HEAP2 PARTS HR1 HPL) as (SA0 & SAC & SAI & (qs & As & ns & Hins & Ra1 & Ra2)).
    set (b := getbn rr bs) in *.
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
    zstep. zstep.
    ihere. to_implM. rewrite K1, K2'. cbn [embed interp]. apply implM_interp_ret.
    eapply evt_cut.
    { eapply (BN_zero_ex_spec (Z_to_bv 64 1091556) (Z_to_bv 64 (bv_unsigned sp + -48))) with (A := R) (D := Dr) (b := b) (lo := lo);
        [exact SR | exact (ref_at_ualign stc OW LB m2 bs PL EA rr R HEAP2 PARTS HR1 NRO) | rewrite ESP; exact ST2 | rewrite ESP; lia | exact MI2 | rewrite ESP; lia | reflexivity]. }
    intros ms' (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & z14 & m3 & -> & MUz & WMz & MIz & STz & SRz).
    rewrite ESP in MUz, STz.
    replace (ret_pc (Z_to_bv 64 1091556)) with (Z_to_bv 64 1091556) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    zstep. zstep. chk ltac:(fun C => clear - C R0 RC; lia). apply evt_done.
    assert (HWL : Forall (w_lib bs OW PL lo (bv_unsigned sp)) [(bv_unsigned sp + -48 - 16, bv_unsigned sp + -48); (R, R + 24)]).
    { constructor; [left; cbn [fst snd]; lia|]. constructor; [|constructor].
      right; left. exists (qs, As, ns). cbn [blk_addr blk_size fst snd]. split; [exact Hins | lia]. }
    assert (WOK : Forall (w_ok OW LB bs PL EA (bv_unsigned sp) [rr]) [(bv_unsigned sp + -48 - 16, bv_unsigned sp + -48); (R, R + 24)]).
    { constructor; [apply w_stack; cbn; lia|]. constructor; [|constructor].
      eapply (w_struct OW LB bs PL EA (bv_unsigned sp) false [rr] _ rr R); [left; reflexivity | exact HR1 | exact NRO | cbn; lia | cbn; lia]. }
    assert (ENV3 : cenv LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -48) s bs OW m [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
                        stc (setbn rr (bn_zero_pure b) bs) m3 OW).
    { apply cenv_setbn.
      eapply (cenv_silent LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -48) s bs OW m CEIL GLO' FBlo FBsp SPB FROK) with (errv' := errv2);
        [exact ENV1 | exact LS1 | exact MUz | exact WMz | exact HWL | exact STz | | exact MIz | | cbn; lia].
      - eapply rw_cells_transport; [exact ERR2 | exact MUz | exact WMz |]. unfold LX_ERRNO, RATP. cbn. clear - SAI SA0 GLO' LOF SPR; unfold GLOBALS_TOP in *; lia.
      - eapply rw_cells_transport; [exact FR2 | exact MUz | exact WMz |]. cbn. lia. }
    unfold add_join. do 18 eexists. exists m3, OW. split; [reflexivity|]. cbn [fst snd].
    split; [exact ENV3|]. split; [|apply ref_at_setbn; exact HR1].
    unfold lib_state. eapply (lib_state_close [] bs m3 OW PL EA rr R); [| exact ND2 | exact HR1 | exact NRO | | |].
    - eapply (lib_state_frame stc LB (bv_unsigned sp) B); [exact HEAP2| exact LSH| exact MUz| exact WMz| exact FROK| exact WOK].
    - exists Dr. split; [exact SRz|]. eapply bn_arr_of_u64arr; [exact ARR|].
      eapply u64arr_transport; [exact U | exact MUz | exact WMz |]. cbn [disjoint_from]. rewrite LENW. clear - DSEP D0 DC LO SPR CEIL; lia.
    - destruct OKR as (O1 & O2 & O3 & O4). unfold bg_ok, bn_zero_pure, bn_dmax in *. cbn [bn_top bn_buf bn_flags]. repeat split; [exact O1 | lia | exact O3 | exact O4].
    - apply ids_ok_setbn_same; [exact IDS | exact HVR | reflexivity].
  Qed.
End Proofs.
End WithCeiling0.
