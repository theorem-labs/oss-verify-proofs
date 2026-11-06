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
From OSSVerify.Proofs.openssl.bndiv.lib.MallocP Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import BnBase BnWords BnWordsCorrect BnModel BnTree BnInv BnSpecs BnAddSpec BnMInv BnBridge.
From OSSVerify.Proofs.openssl.bndiv.lib.P Require Import Layout Lib_iface Lib_kit.
From OSSVerify.Proofs.openssl.bndiv.lib.BnW Require Import BnTac BnMem BnTacX.
From OSSVerify.Proofs.openssl.bndiv.lib.BnP Require Import BnKit BnHeap BnArr BnRep BnIface W_small W_small2 W_expand BnCall.
From OSSVerify.Proofs.openssl.bndiv.lib.BnA Require Import BnAPure BnAKit W_cmp W_uadd W_usub.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.openssl.bndiv.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition BN_ADD : Z := 0x10ca94.
Definition BN_ADD_STACK : Z := 48 + BN_UADD_STACK.

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  (* [comment removed for export] *)
  Lemma add_fin : forall
      (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (m : mem) (s : PState) (ls : lstate bptr) (OW LB : list block) (AD : bn_addrs) (EA : err_addrs) (lo B : Z)
      (st : PState) (lsx : lstate bptr) (mx : mem) (OWx : list block) (rneg : bool) (rr : bnref) (R : Z)
      (x1 t0 t1 t2 x8 a1 a2 a3 a4 a5 a6 a7 x18 x19 t3 t4 t5 t6 : word),
    cenv LB AD lo B (bv_unsigned sp) (bv_unsigned sp + -48) s ls OW m [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] st lsx mx OWx ->
    lib_state lsx mx OWx AD EA ->
    alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - 48 -> bv_unsigned sp <= B ->
    ref_at lsx OWx AD rr R ->
    evt psegs (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s ls OW LB lo B m AD EA (fun _ _ _ a0' => a0' = wz 1)
                       (tt, setbn rr (bn_with_neg (getbn rr lsx) rneg) lsx) st)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp (wz RATP) t0 t1 t2 x8 (Z_to_bv 64 R) (wz 1) a1 a2 a3 a4 a5 a6 a7
               x18 x19 (Z_to_bv 64 (Z.b2z rneg)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x10cb1c) fc None mx (seg_rom psegs)).
  Proof.
    intros until t6. intros ENV LS CEIL GLO LO SPB HR.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof ENV as (HEAP & AUX & ST & (errv & ERR) & MI & LXP & FA & SO & RS & FR & _).
    unfold LX_ERRNO, RATP in ERR. change (3063480 - 164) with 3063316 in ERR.
    pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
    destruct (lib_state_open [] lsx mx OWx AD EA rr R LS ND HR ltac:(intros [])) as ((Dr & SR & ARR) & OKR & LSH).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HR) as HVR.
    destruct (lib_state_h_parts _ _ _ _ _ _ LS) as (IDS & ADB & ERRB & SOK).
    destruct (bn_arr_facts st OWx LB mx HEAP lsx AD EA IDS ADB rr Dr HVR ARR) as (U & LENW & D0 & DC & DI & DSEP).
    specialize (DSEP rr R HR).
    destruct (ref_at_inb _ _ _ _ _ ADB HR) as (qs & As & ns & _ & Hins & Ra1 & Ra2).
    pose proof (RH_range _ _ _ _ _ _ _ HEAP Hins) as (SA0 & _ & _ & SAC & SAI).
    set (b := getbn rr lsx) in *.
    unfold bn_cells, MallocRep.wz in SR. unfold GLOBALS_TOP in GLO.
    pose proof (munch_refl [(R, R + 24)]%Z mx) as MU. pose proof (wmono_refl psegs mx) as WM.
    zstep.
    do 6 zstep. release_frame FR ST (bv_unsigned sp). zstep. zstep.
    apply evt_done.
    lazymatch goal with |- bn_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (MS _ _ _ _ _ ?mf _) => rename mf into mF end.
    assert (HWL : Forall (w_lib OWx lo (bv_unsigned sp)) [(R, R + 24)]).
    { constructor; [right; exists (qs, As, ns); cbn [blk_addr blk_size fst snd]; split; [exact Hins | lia] | constructor]. }
    assert (WOK : Forall (w_ok OWx LB lsx AD EA [rr]) [(R, R + 24)]).
    { constructor; [eapply (w_struct OWx LB lsx AD EA false [rr] _ rr R); [left; reflexivity | exact HR | cbn; lia | cbn; lia] | constructor]. }
    unfold bn_post. do 15 eexists. exists mF, OWx, errv. split; [reflexivity|]. cbn [fst snd].
    split; [exact (seg_heap _ _ _ _ _ _ _ _ HEAP MU WM HWL CEIL)|].
    split.
    { unfold lib_state. eapply (lib_state_close [] lsx mF OWx AD EA rr R); [| exact ND | exact HR | | |].
      - eapply lib_state_frame; [exact HEAP | exact LSH | exact MU | exact WM | exact WOK].
      - exists Dr. split; [unfold bn_cells, bn_with_neg, bn_dmax; cbn [bn_top bn_buf bn_neg bn_flags]; exact SR|].
        eapply bn_arr_of_u64arr; [exact ARR | exact U].
      - destruct OKR as (O1 & O2 & O3 & O4). unfold bn_okm, bn_with_neg, bn_dmax in *. cbn [bn_top bn_buf bn_flags]. auto.
      - apply ids_ok_setbn_same; [exact IDS | exact HVR | reflexivity]. }
    split; [apply (seg_auxv _ _ _ _ _ _ _ _ _ HEAP AUX MU WM HWL SPB); unfold GLOBALS_TOP; lia|].
    split; [exact ST|]. split; [unfold LX_ERRNO, RATP; exact ERR|]. split; [exact MI|].
    split. { eapply lx_pres_trans; [exact LXP|]. apply (seg_lx_pres _ _ _ _ _ _ _ _ _ HEAP MU WM HWL CEIL); [unfold GLOBALS_TOP; lia | lia]. }
    split; [exact FA|]. split; [exact SO|].
    split. { intros r0 a0' H0. apply ref_at_setbn. apply RS. exact H0. }
    reflexivity.
  Qed.

  (* [comment removed for export] *)
  Definition add_join (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (m : mem) (s : PState) (ls : lstate bptr) (OW LB : list block) (AD : bn_addrs) (EA : err_addrs) (lo B : Z) (rr : bnref) (R : Z)
      (v : bool * lstate bptr) (st' : PState) : machine_state -> Prop :=
    fun ms' => exists x1 t0 t1 t2 x8 a1 a2 a3 a4 a5 a6 a7 x18 x19 t3 t4 t5 t6 m' OW',
      ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp (wz RATP) t0 t1 t2 x8 (Z_to_bv 64 R) (wz 1) a1 a2 a3 a4 a5 a6 a7
                    x18 x19 (Z_to_bv 64 (Z.b2z (fst v))) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x10cb1c) fc None m' (seg_rom psegs)
      /\ cenv LB AD lo B (bv_unsigned sp) (bv_unsigned sp + -48) s ls OW m [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] st' (snd v) m' OW'
      /\ lib_state (snd v) m' OW' AD EA /\ ref_at (snd v) OW' AD rr R.

  (* [comment removed for export] *)
  Lemma add_usub_path : forall
      (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (m : mem) (s : PState) (ls : lstate bptr) (OW LB : list block) (AD : bn_addrs) (EA : err_addrs) (lo B : Z)
      (st : PState) (lsx : lstate bptr) (mx : mem) (OWx : list block) (n : bool) (rr p q : bnref) (R P Q : Z)
      (x1 t0 t1 t2 x8 a3 a4 a5 a6 a7 x18 x19 t3 t4 t5 t6 : word),
    cenv LB AD lo B (bv_unsigned sp) (bv_unsigned sp + -48) s ls OW m [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] st lsx mx OWx ->
    lib_state lsx mx OWx AD EA ->
    alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - BN_ADD_STACK -> bv_unsigned sp <= B ->
    ref_at lsx OWx AD rr R -> ref_at lsx OWx AD p P -> ref_at lsx OWx AD q Q ->
    implM psegs (interp (embed (tbind (BN_usub (tree_ops bptr) rr p q lsx) (fun p0 : unit * lstate bptr => TRet (n, snd p0))))) st
      (add_join ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s ls OW LB AD EA lo B rr R)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp (wz RATP) t0 t1 t2 x8 (Z_to_bv 64 R) (Z_to_bv 64 R) (Z_to_bv 64 P) (Z_to_bv 64 Q)
               a3 a4 a5 a6 a7 x18 x19 (Z_to_bv 64 (Z.b2z n)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x10cb00) fc None mx (seg_rom psegs)).
  Proof.
    intros until t6. intros ENV LS CEIL GLO LO SPB HR HP HQ.
    unfold BN_ADD_STACK, BN_UADD_STACK, BN_WEXPAND_STACK, BN_EXPAND2_STACK in LO.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (FBlo : lo <= bv_unsigned sp + -48) by lia.
    assert (FBsp : bv_unsigned sp + -48 <= bv_unsigned sp) by lia.
    assert (SPR2 : bv_unsigned sp < 2 ^ 64) by lia.
    pose proof (cenv_pre LB AD EA lo B (bv_unsigned sp) (bv_unsigned sp + -48) s ls OW m CEIL GLO FBlo FBsp SPB SPR2) as CPRE.
    pose proof (cenv_post LB AD EA lo B (bv_unsigned sp) (bv_unsigned sp + -48) s ls OW m CEIL GLO FBlo FBsp) as CPOST.
    pose proof (fun A => @bn_post_cpost _ _ LB AD EA lo B (bv_unsigned sp) (bv_unsigned sp + -48) CEIL FBlo FBsp SPR2 A) as BPC.
    unfold implM. iprefix. zstep.
    destruct (CPRE _ _ _ _ _ BN_USUB_STACK ENV LS ltac:(unfold BN_USUB_STACK, BN_WEXPAND_STACK, BN_EXPAND2_STACK; lia)) as (errv1 & PRE1).
    ihere. to_implM.
    eapply implM_embed_bind.
    { eapply (BN_usub_walk HM HF) with (lo := lo) (B := B) (errv := errv1) (OW := OWx) (LB := LB) (AD := AD) (EA := EA)
        (rr := rr) (x := p) (y := q) (R := R) (X := P) (Y := Q);
        [exact PRE1 | reflexivity | exact HR | exact HP | exact HQ | reflexivity | reflexivity | reflexivity]. }
    cbv beta. intros [[] lsu] stu msu PO. apply BPC in PO. cbn [fst snd] in PO.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m2 & OW1 & -> & CP & (-> & _)).
    destruct (CPOST _ _ _ _ _ _ _ _ _ ENV CP) as (ENV1 & LS1).
    pose proof (cpost_refs LB AD EA lo B (bv_unsigned sp + -48) _ _ _ _ _ _ _ _ CP) as RS.
    replace (ret_pc (Z_to_bv 64 1100548)) with (Z_to_bv 64 1100548) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    cbn [embed interp fst snd]. apply implM_interp_ret.
    zstep. apply evt_done.
    unfold add_join. do 18 eexists. exists m2, OW1. split; [reflexivity|]. cbn [fst snd].
    split; [exact ENV1|]. split; [exact LS1 | apply RS; exact HR].
  Qed.

  Lemma BN_add_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (ls : lstate bptr) (OW LB : list block) (AD : bn_addrs) (EA : err_addrs)
      (lo B : Z) (errv : word) (rr x y : bnref) (R X Y : Z),
    bn_pre s ls m OW LB AD EA sp lo B errv BN_ADD_STACK -> tp = wz RATP ->
    ref_at ls OW AD rr R -> ref_at ls OW AD x X -> ref_at ls OW AD y Y ->
    a0 = wz R -> a1 = wz X -> a2 = wz Y ->
    implM psegs (interp (embed (BN_add (tree_ops bptr) rr x y ls))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s ls OW LB lo B m AD EA (fun _ _ _ a0' => a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_ADD) fc None m (seg_rom psegs)).
  Proof.
    intros until Y. intros PRE -> HR HX HY -> -> ->.
    pose proof PRE as (HEAP & LS & AUX & SPB & ST & CEIL & GLO & LO & ERR & MI).
    unfold BN_ADD_STACK, BN_UADD_STACK, BN_WEXPAND_STACK, BN_EXPAND2_STACK in LO.
    unfold BN_ADD, MallocRep.wz.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    destruct (open_ro s OW LB m ls AD EA x X HEAP LS HX) as (Dx0 & SX & OKX & _ & X0 & XC & _).
    destruct (open_ro s OW LB m ls AD EA y Y HEAP LS HY) as (Dy0 & SY & OKY & _ & Y0 & YC & _).
    unfold bn_cells, MallocRep.wz in SX, SY.
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl psegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3063480 - 164) with 3063316 in ERR.
    assert (GLO' : GLOBALS_TOP <= lo) by exact GLO. unfold GLOBALS_TOP in GLO.
    unfold BN_add, bbind, bget, bset, bret. cbn [bind ret tree_ops tbind fst snd].
    set (na := bn_neg (getbn x ls)) in *. set (nb := bn_neg (getbn y ls)) in *.
    assert (NA : 0 <= Z.b2z na <= 1) by (destruct na; cbn; lia).
    assert (NB : 0 <= Z.b2z nb <= 1) by (destruct nb; cbn; lia).
    unfold implM. iprefix.
    carve_frame 48%nat ST. do 8 zstep.
    do 2 zstep.
    zstep. rewrite (sx32_small (Z.b2z na)) by (clear - NA; lia).
    zstep. rewrite (sx32_small (Z.b2z nb)) by (clear - NB; lia).
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HWL0 : Forall (w_lib OW lo (bv_unsigned sp)) [(bv_unsigned sp + -48, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
    assert (WOK0 : Forall (w_ok OW LB ls AD EA []) [(bv_unsigned sp + -48, bv_unsigned sp)]) by (constructor; [apply w_stack; cbn; lia| constructor]).
    pose proof (lib_state_frame s LB [] ls m m1 OW AD EA _ HEAP LS MU WM WOK0) as LS0.
    lazymatch type of FR with rw_cells _ _ _ ?fr =>
      assert (ENV : cenv LB AD lo B (bv_unsigned sp) (bv_unsigned sp + -48) s ls OW m fr s ls m1 OW)
    end.
    { unfold cenv. split; [exact (seg_heap _ _ _ _ _ _ _ _ HEAP MU WM HWL0 CEIL)|].
      split; [apply (seg_auxv _ _ _ _ _ _ _ _ _ HEAP AUX MU WM HWL0 SPB); exact GLO'|].
      split; [exact ST|]. split; [exists errv; unfold LX_ERRNO, RATP; exact ERR|]. split; [exact MI|].
      split; [apply (seg_lx_pres _ _ _ _ _ _ _ _ _ HEAP MU WM HWL0 CEIL GLO'); lia|].
      split; [reflexivity|]. split; [reflexivity|]. split; [apply refs_stable_refl|]. split; [exact FR| cbn; lia]. }
    assert (FBlo : lo <= bv_unsigned sp + -48) by lia.
    assert (FBsp : bv_unsigned sp + -48 <= bv_unsigned sp) by lia.
    assert (SPR2 : bv_unsigned sp < 2 ^ 64) by lia.
    pose proof (cenv_pre LB AD EA lo B (bv_unsigned sp) (bv_unsigned sp + -48) s ls OW m CEIL GLO' FBlo FBsp SPB SPR2) as CPRE.
    pose proof (cenv_post LB AD EA lo B (bv_unsigned sp) (bv_unsigned sp + -48) s ls OW m CEIL GLO' FBlo FBsp) as CPOST.
    pose proof (fun A => @bn_post_cpost _ _ LB AD EA lo B (bv_unsigned sp) (bv_unsigned sp + -48) CEIL FBlo FBsp SPR2 A) as BPC.
    assert (LOF : lo <= bv_unsigned sp - 48) by lia.
    clear HEAP LS AUX ST ERR MI MU WM HWL0 WOK0 FR PRE SX SY.
    zstep. if_cases K; zify_cond K.
    2:{ (* [comment removed for export] *)
      replace (eqb na nb) with true by (symmetry; clear - K; destruct na, nb; cbn in *; congruence).
      do 4 zstep.
      destruct (CPRE _ _ _ _ _ BN_UADD_STACK ENV LS0 ltac:(unfold BN_UADD_STACK, BN_WEXPAND_STACK, BN_EXPAND2_STACK; lia)) as (errv1 & PRE1).
      ihere. to_implM.
      eapply implM_embed_bind with (Q1 := fun (v : bool * lstate bptr) st' ms' => fst v = na /\
          bn_post (Z_to_bv 64 1100508) (Z_to_bv 64 (bv_unsigned sp + -48)) gp sp (Z_to_bv 64 R) (Z_to_bv 64 Y) (Z_to_bv 64 X)
                  (Z_to_bv 64 (Z.b2z na)) s5 s6 s7 s8 s9 s10 s11 F fc s ls OW LB lo B m1 AD EA (uarith_res rr ls OW) (tt, snd v) st' ms').
      { eapply implM_embed_bind.
        { eapply (BN_uadd_walk HM HF) with (lo := lo) (B := B) (errv := errv1) (OW := OW) (LB := LB) (AD := AD) (EA := EA)
            (rr := rr) (ra_ := x) (rb_ := y) (R := R) (A := X) (Bb := Y);
            [exact PRE1 | reflexivity | exact HR | exact HX | exact HY | reflexivity | reflexivity | reflexivity]. }
        cbv beta. intros [[] lsu] stu msu PO. cbn [embed interp fst snd]. apply implM_interp_ret. apply evt_done.
        split; [reflexivity | exact PO]. }
      cbv beta. intros [rn lsu] stu msu [Ern PO]. cbn [fst snd] in *. subst rn. apply BPC in PO.
      destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m2 & OW1 & -> & CP & (-> & _)).
      destruct (CPOST _ _ _ _ _ _ _ _ _ ENV CP) as (ENV1 & LS1).
      pose proof (cpost_refs LB AD EA lo B (bv_unsigned sp + -48) _ _ _ _ _ _ _ _ CP) as RS.
      cbn [fst snd] in *.
      replace (ret_pc (Z_to_bv 64 1100508)) with (Z_to_bv 64 1100508) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      cbn [embed interp]. apply implM_interp_ret.
      zstep.
      eapply add_fin; [exact ENV1 | exact LS1 | exact CEIL | exact GLO' | exact LOF | exact SPB | apply RS; exact HR]. }
    (* [comment removed for export] *)
    replace (eqb na nb) with false by (symmetry; clear - K; destruct na, nb; cbn in *; congruence).
    do 3 zstep.
    destruct (CPRE _ _ _ _ _ BN_UCMP_STACK ENV LS0 ltac:(unfold BN_UCMP_STACK; lia)) as (errv1 & PRE1).
    ihere. to_implM.
    eapply implM_embed_bind with (Q1 := add_join ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s ls OW LB AD EA lo B rr R).
    2:{ cbv beta. intros [rn lsu] stu msu (x1 & u0 & u1 & u2 & x8 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & x18 & x19 & u3 & u4 & u5 & u6 & m' & OW' & -> & ENV' & LS' & HR').
        cbn [fst snd] in *. cbn [embed interp]. apply implM_interp_ret.
        eapply add_fin; [exact ENV' | exact LS' | exact CEIL | exact GLO' | exact LOF | exact SPB | exact HR']. }
    eapply implM_embed_bind.
    { eapply BN_ucmp_walk with (lo := lo) (B := B) (errv := errv1) (OW := OW) (LB := LB) (AD := AD) (EA := EA) (r1 := x) (r2 := y) (a := X) (b := Y);
        [exact PRE1 | reflexivity | exact HX | exact HY | reflexivity | reflexivity]. }
    cbv beta. intros [c lsc] stc msc PO. apply BPC in PO. cbn [fst snd] in PO.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m2 & OW1 & -> & CP & ((-> & CR & -> & ->) & EC)).
    destruct (CPOST _ _ _ _ _ _ _ _ _ ENV CP) as (ENV1 & LS1).
    pose proof (cpost_refs LB AD EA lo B (bv_unsigned sp + -48) _ _ _ _ _ _ _ _ CP) as RS.
    cbn [fst snd] in *.
    replace (ret_pc (Z_to_bv 64 1100524)) with (Z_to_bv 64 1100524) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    clear PRE1 CP ENV LS0 EC.
    unfold implM. iprefix.
    pose proof ENV1 as (HEAP2 & _ & ST2 & _ & MI2 & _).
    pose proof (RS _ _ HR) as HR1. pose proof (RS _ _ HX) as HX1. pose proof (RS _ _ HY) as HY1.
    destruct (open_ro stc OW LB m2 ls AD EA x X HEAP2 LS1 HX1) as (Dx1 & SX & _).
    destruct (open_ro stc OW LB m2 ls AD EA y Y HEAP2 LS1 HY1) as (Dy1 & SY & _).
    unfold bn_cells, MallocRep.wz in SX, SY. fold na in SX. fold nb in SY.
    zstep. if_cases K1; zify_cond K1.
    2:{ (* [comment removed for export] *)
      assert (K1' : (0 <? c) = true) by (rewrite <- (land64_pos_iff c) by (clear - CR; lia); apply andb_true_iff; split; apply Z.ltb_lt; assumption).
      zstep. rewrite (sx32_small (Z.b2z na)) by (clear - NA; lia).
      do 3 zstep.
      ihere. to_implM. rewrite K1'.
      eapply add_usub_path; [exact ENV1 | exact LS1 | exact CEIL | exact GLO' | | exact SPB | exact HR1 | exact HX1 | exact HY1].
      unfold BN_ADD_STACK, BN_UADD_STACK, BN_WEXPAND_STACK, BN_EXPAND2_STACK. lia. }
    rewrite land64_pos_iff in K1 by (clear - CR; lia).
    zstep. if_cases K2; zify_cond K2.
    { (* [comment removed for export] *)
      rewrite land64_neg_iff in K2 by (clear - CR; lia).
      assert (K2' : (c <? 0) = true) by (apply Z.ltb_lt; exact K2).
      zstep. rewrite (sx32_small (Z.b2z nb)) by (clear - NB; lia).
      do 4 zstep.
      ihere. to_implM. rewrite K1, K2'.
      eapply add_usub_path; [exact ENV1 | exact LS1 | exact CEIL | exact GLO' | | exact SPB | exact HR1 | exact HY1 | exact HX1].
      unfold BN_ADD_STACK, BN_UADD_STACK, BN_WEXPAND_STACK, BN_EXPAND2_STACK. lia. }
    (* [comment removed for export] *)
    assert (K2' : (c <? 0) = false).
    { apply Z.ltb_ge. destruct (Z_lt_ge_dec c 0) as [Hc|Hc]; [|lia]. exfalso.
      apply (land64_neg_iff c ltac:(clear - CR; lia)) in Hc. clear - Hc K2. lia. }
    pose proof ENV1 as (_ & _ & _ & (errv2 & ERR2) & _ & _ & _ & _ & _ & FR2 & _).
    pose proof (RH_nodup_l _ _ _ _ HEAP2) as ND2.
    destruct (lib_state_open [] ls m2 OW AD EA rr R LS1 ND2 HR1 ltac:(intros [])) as ((Dr & SR & ARR) & OKR & LSH).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS1 HR1) as HVR.
    destruct (lib_state_h_parts _ _ _ _ _ _ LS1) as (IDS & ADB & ERRB & SOK).
    destruct (bn_arr_facts stc OW LB m2 HEAP2 ls AD EA IDS ADB rr Dr HVR ARR) as (U & LENW & D0 & DC & DI & DSEP).
    specialize (DSEP rr R HR1).
    destruct (ref_at_inb _ _ _ _ _ ADB HR1) as (qs & As & ns & _ & Hins & Ra1 & Ra2).
    pose proof (RH_range _ _ _ _ _ _ _ HEAP2 Hins) as (SA0 & _ & _ & SAC & SAI).
    set (b := getbn rr ls) in *.
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
    zstep. zstep.
    ihere. to_implM. rewrite K1, K2'. cbn [embed interp]. apply implM_interp_ret.
    eapply evt_cut.
    { eapply (BN_zero_ex_spec (Z_to_bv 64 1100564) (Z_to_bv 64 (bv_unsigned sp + -48))) with (A := R) (D := Dr) (b := b) (lo := lo);
        [exact SR | rewrite ESP; exact ST2 | rewrite ESP; lia | exact MI2 | rewrite ESP; lia | reflexivity]. }
    intros ms' (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & z14 & m3 & -> & MUz & WMz & MIz & STz & SRz).
    rewrite ESP in MUz, STz.
    replace (ret_pc (Z_to_bv 64 1100564)) with (Z_to_bv 64 1100564) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    zstep. zstep. apply evt_done.
    assert (HWL : Forall (w_lib OW lo (bv_unsigned sp)) [(bv_unsigned sp + -48 - 16, bv_unsigned sp + -48); (R, R + 24)]).
    { constructor; [left; cbn [fst snd]; lia|]. constructor; [|constructor].
      right. exists (qs, As, ns). cbn [blk_addr blk_size fst snd]. split; [exact Hins | lia]. }
    assert (WOK : Forall (w_ok OW LB ls AD EA [rr]) [(bv_unsigned sp + -48 - 16, bv_unsigned sp + -48); (R, R + 24)]).
    { constructor; [apply w_stack; cbn; lia|]. constructor; [|constructor].
      eapply (w_struct OW LB ls AD EA false [rr] _ rr R); [left; reflexivity | exact HR1 | cbn; lia | cbn; lia]. }
    assert (ENV3 : cenv LB AD lo B (bv_unsigned sp) (bv_unsigned sp + -48) s ls OW m [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
                        stc (setbn rr (bn_zero_pure b) ls) m3 OW).
    { apply cenv_setbn.
      eapply (cenv_silent LB AD lo B (bv_unsigned sp) (bv_unsigned sp + -48) s ls OW m CEIL GLO' FBlo FBsp SPB) with (errv' := errv2);
        [exact ENV1 | exact MUz | exact WMz | exact HWL | exact STz | | exact MIz | | cbn; lia].
      - eapply rw_cells_transport; [exact ERR2 | exact MUz | exact WMz |]. unfold LX_ERRNO, RATP. cbn. lia.
      - eapply rw_cells_transport; [exact FR2 | exact MUz | exact WMz |]. cbn. lia. }
    unfold add_join. do 18 eexists. exists m3, OW. split; [reflexivity|]. cbn [fst snd].
    split; [exact ENV3|]. split; [|apply ref_at_setbn; exact HR1].
    unfold lib_state. eapply (lib_state_close [] ls m3 OW AD EA rr R); [| exact ND2 | exact HR1 | | |].
    - eapply lib_state_frame; [exact HEAP2 | exact LSH | exact MUz | exact WMz | exact WOK].
    - exists Dr. split; [exact SRz|]. eapply bn_arr_of_u64arr; [exact ARR|].
      eapply u64arr_transport; [exact U | exact MUz | exact WMz |]. cbn [disjoint_from]. rewrite LENW. lia.
    - destruct OKR as (O1 & O2 & O3 & O4). unfold bn_okm, bn_zero_pure, bn_dmax in *. cbn [bn_top bn_buf bn_flags]. repeat split; [exact O1 | lia | exact O3 | exact O4].
    - apply ids_ok_setbn_same; [exact IDS | exact HVR | reflexivity].
  Qed.
End Proofs.
End WithCeiling0.
