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
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Import Layout Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnMem BnTacX.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BnDivWords BnDivLoop.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require BnSpecs2 BnDivSpec.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnArith.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnWU Require Import BnUTac.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnWU Require Import WU_num_bits_word.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr DivLoopPure DivTop.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnP Require DivLA.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnP Require Import DivBody DivLoop.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require Import BnHeap DivLA DivBody DivLoop BnAssoc.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require BnRep BnLeaves.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BgState BgInv BgLib BgArith.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgRepU Require Import BgRepDefs BgRep BgLayer BgIface BnUAlign.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnRU Require Import BgLeaves W_expand W_ctx W_ctx_get W_copy BnCall BnRKit W_lshift W_rshift W_ctx_end W_div_tail W_div_pad BnUJoin.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnR Require Import BgLive DivModel.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Local Notation ops := (tree_ops bptr).

Lemma la_run : forall r (bs : bstate bptr),
  bn_left_align ops r bs =
  TRet (64 - num_bits_word (nth (bn_top (getbn r bs) - 1) (bn_buf (getbn r bs)) 0),
        setbn r (bn_with_buf (getbn r bs) (splice (bn_buf (getbn r bs)) 0
                   (fst (lshift_limbs (firstn (bn_top (getbn r bs)) (bn_buf (getbn r bs))) (64 - num_bits_word (nth (bn_top (getbn r bs) - 1) (bn_buf (getbn r bs)) 0)) 0)))) bs).
Proof. reflexivity. Qed.

Lemma bbind_get_set : forall {B} r (g : bignum bptr -> bignum bptr) (f : unit -> BM (M := btree bptr) B) (bs : bstate bptr),
  bbind ops (bbind ops (bget ops r) (fun b => bset ops r (g b))) f bs =
  f tt (setbn r (g (getbn r bs)) bs).
Proof. reflexivity. Qed.

Definition div_core (res tmp snum sdiv : bnref) (rm : option bnref) (num divisor : bnref) : BM (M:=btree bptr) (ptr:=bptr) unit :=
  bbind ops (BN_copy ops sdiv divisor) (fun _ =>
  bbind ops (bn_left_align ops sdiv) (fun norm_shift =>
  bbind ops (bbind ops (bget ops sdiv) (fun b => bset ops sdiv (bn_with_neg b false))) (fun _ =>
  bbind ops (bn_lshift_fixed_top ops snum num norm_shift) (fun _ =>
  bbind ops (bget ops sdiv) (fun sd =>
  bbind ops (bget ops snum) (fun sn =>
  let div_n := bn_top sd in
  bbind ops (if (bn_top sn <=? div_n)%nat then
     bbind ops (bn_wexpand ops snum (div_n + 1)) (fun _ =>
     bbind ops (bget ops snum) (fun sn' =>
     bset ops snum (mkBN (bn_d sn') (splice (bn_buf sn') (bn_top sn) (repeat 0 (div_n - bn_top sn + 1)))
                     (div_n + 1) (bn_neg sn') (bn_flags sn'))))
   else bret ops tt) (fun _ =>
  bbind ops (bget ops snum) (fun sn =>
  let num_n := bn_top sn in
  let loop := (num_n - div_n)%nat in
  let d0 := nth (div_n - 1) (bn_buf sd) 0 in
  let d1 := if (div_n =? 1)%nat then 0 else nth (div_n - 2) (bn_buf sd) 0 in
  bbind ops (bn_wexpand ops res loop) (fun _ =>
  bbind ops (bget ops num) (fun nm =>
  bbind ops (bget ops divisor) (fun dvs =>
  let num_neg := bn_neg nm in
  bbind ops (bbind ops (bget ops res) (fun r => bset ops res (mkBN (bn_d r) (bn_buf r) loop (xorb num_neg (bn_neg dvs)) (bn_flags r)))) (fun _ =>
  bbind ops (bn_wexpand ops tmp (div_n + 1)) (fun _ =>
  bbind ops (bget ops snum) (fun sn =>
  bbind ops (bget ops tmp) (fun tm =>
  bbind ops (bget ops res) (fun r =>
  let '(snb, tmb, rb) := div_loop (bn_buf sd) div_n loop num_n d0 d1 loop 0 (bn_buf sn, bn_buf tm, bn_buf r) in
  bbind ops (bset ops tmp (bn_with_buf tm tmb)) (fun _ =>
  bbind ops (bset ops res (bn_with_buf r rb)) (fun _ =>
  bbind ops (bset ops snum (mkBN (bn_d sn) snb div_n num_neg (bn_flags sn))) (fun _ =>
  bbind ops (match rm with Some r => bn_rshift_fixed_top ops r snum norm_shift | None => bret ops tt end) (fun _ =>
  BN_CTX_end ops)))))))))))))))))))).

Definition div_rest (res : bnref) (rm : option bnref) (num divisor : bnref) : BM (M:=btree bptr) (ptr:=bptr) unit :=
  bbind ops (BN_CTX_get ops) (fun tmp =>
  bbind ops (BN_CTX_get ops) (fun snum =>
  bbind ops (BN_CTX_get ops) (fun sdiv => div_core res tmp snum sdiv rm num divisor))).

Lemma bn_div_fixed_top_unfold : forall dv rm num divisor,
  bn_div_fixed_top ops dv rm num divisor =
  bn_live ops (num :: divisor :: opt_refs dv ++ opt_refs rm) (
  bbind ops (BN_CTX_start ops) (fun _ =>
  bbind ops (match dv with None => BN_CTX_get ops | Some r => bret ops r end) (fun res => div_rest res rm num divisor))).
Proof. reflexivity. Qed.

Ltac split_cell L c k :=
  lazymatch L with
  | c :: ?post => k (@nil cell) post
  | ?x :: ?rest => split_cell rest c ltac:(fun pre post => k (x :: pre) post)
  end.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition BN_DIV_FIXED_TOP : Z := 0x1097c8.
Definition BN_DIV_STACK : Z := 256 + 16384.

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Lemma bn_div_fixed_top_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (dv rm : option bnref) (num dvs : bnref) (adv arm anum advs ac : Z) (qc : bptr),
    bn_pre s bs m OW LB PL EA sp lo B errv BN_DIV_STACK -> tp = wz RATP -> pl_ctx PL = Some (ac, qc) ->
    oref_at bs OW PL dv adv -> oref_at bs OW PL rm arm -> ref_at bs OW PL num anum -> ref_at bs OW PL dvs advs ->
    (forall d, dv = Some d -> wref PL d) -> (forall r, rm = Some r -> hpl PL r) -> num <> ROne -> dvs <> ROne ->
    a0 = wz adv -> a1 = wz arm -> a2 = wz anum -> a3 = wz advs -> a4 = wz ac ->
    (1 <= bn_top (getbn dvs bs))%nat -> nth (bn_top (getbn dvs bs) - 1) (bn_buf (getbn dvs bs)) 0 <> 0 ->
    implM bgusegs (interp (embed (bn_div_fixed_top ops dv rm num dvs bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA
               (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_DIV_FIXED_TOP) fc None m (seg_rom bgusegs)).
  Proof.
    intros until qc. intros PRE -> EC HAdv HArm HAnum HAdvs WRdv HPrm NROn NROd -> -> -> -> -> HTOPD HTOPNZ.
    pose proof PRE as (HEAP & LS & FROK & AUX & SPB & B63 & ST & CEIL & GLO & LO & ERR & MI).
    unfold BN_DIV_STACK, BN_DIV_FIXED_TOP, GLOBALS_TOP, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.

    rewrite bn_div_fixed_top_unfold, bn_live_run.
    destruct (live_refs (st_ctx bs) (num :: dvs :: opt_refs dv ++ opt_refs rm)) eqn:LIVE; [| cbn [embed interp]; apply implM_interp_unr].
    apply live_refs_true_iff in LIVE.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS0. pose proof PARTS0 as (WFS0 & _).
    destruct (st_wf_get_pre bs WFS0) as (_ & _ & EPU0).
    assert (LVn : (num < NFIX + gx_pused (st_ctx bs))%nat) by (rewrite EPU0; exact (Forall_inv LIVE)).
    assert (LVd : (dvs < NFIX + gx_pused (st_ctx bs))%nat) by (rewrite EPU0; exact (Forall_inv (Forall_inv_tail LIVE))).
    assert (LVv : forall d, dv = Some d -> (d < NFIX + gx_pused (st_ctx bs))%nat).
    { intros d ->. rewrite EPU0. cbn [opt_refs app] in LIVE. exact (Forall_inv (Forall_inv_tail (Forall_inv_tail LIVE))). }
    clear LIVE EPU0 WFS0 PARTS0.
    pose proof (munch_refl [(bv_unsigned sp - 256, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgusegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3346328 - 164) with 3346164 in ERR.
    unfold implM. iprefix.
    carve_frame 256%nat ST. do 15 step. do 3 step. step. do 3 step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HWL : Forall (w_lib bs OW PL lo (bv_unsigned sp)) [(bv_unsigned sp + -256, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
    assert (WOK : Forall (w_ok OW LB bs PL EA (bv_unsigned sp) []) [(bv_unsigned sp + -256, bv_unsigned sp)]) by (constructor; [apply w_stack; cbn; lia| constructor]).
    pose proof (lib_state_frame s LB _ _ [] bs m m1 OW PL EA _ HEAP LS MU WM FROK WOK) as LS1.
    assert (FBlo : lo <= bv_unsigned sp + -256) by lia.
    assert (FBsp : bv_unsigned sp + -256 <= bv_unsigned sp) by lia.
    assert (SPR2 : bv_unsigned sp < 2 ^ 64) by lia.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
    lazymatch type of FR with rw_cells _ _ _ ?fr =>
      assert (ENV : cenv LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -256) s bs OW m fr s bs m1 OW)
    end.
    { unfold cenv. split; [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL)|].
      split; [apply (seg_auxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK AUX MU WM HWL SPB ltac:(lia)); unfold GLOBALS_TOP; lia|].
      split; [exact ST|]. split; [exists errv; unfold LX_ERRNO, RATP; exact ERR|]. split; [exact MI|].
      split; [apply (seg_lx_pres _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL); unfold GLOBALS_TOP; lia|].
      split; [reflexivity|]. split; [reflexivity|]. split; [apply refs_stable_refl|]. split; [exact FR| cbn; lia]. }
    assert (GLO' : GLOBALS_TOP <= lo) by (unfold GLOBALS_TOP; lia).
    pose proof (cenv_pre LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -256) s bs OW m CEIL GLO' FBlo FBsp SPB SPR2 FROK) as CPRE.
    pose proof (cenv_post LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -256) s bs OW m CEIL GLO' FBlo FBsp FROK) as CPOST.
    pose proof (fun A => @bn_post_cpost _ _ LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -256) CEIL FBlo FBsp SPR2 A) as BPC.
    clear HEAP LS AUX ST ERR MI MU WM HWL WOK FR PRE PARTS.

    destruct (CPRE _ _ _ _ _ BN_CTX_START_STACK ENV LS1 ltac:(unfold BN_CTX_START_STACK; lia)) as (errv1 & PRE1).
    ihere. to_implM. unfold bbind at 1. cbn [bind tree_ops].
    eapply implM_embed_bind.
    { eapply BnLeaves.implM_embed_leaves; [apply (BN_CTX_start_leaves bs)|].
      eapply (BN_CTX_start_walk HM) with (lo := lo) (B := B) (errv := errv1) (OW := OW) (LB := LB) (PL := PL) (EA := EA) (ac := ac) (qc := qc);
        [exact PRE1 | reflexivity | exact EC | reflexivity]. }
    cbv beta. intros [u1 bs2] st2 ms2 [PO LEAF2]. apply BPC in PO.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m2 & OW2 & PL2 & -> & CP2 & (EPL2 & _)).
    subst PL2. specialize (CP2 eq_refl).
    destruct (CPOST _ _ _ _ _ _ _ _ _ ENV CP2) as (ENV2 & LS2).
    pose proof (cpost_refs LB PL EA lo B (bv_unsigned sp + -256) _ _ _ _ _ _ _ _ CP2) as RS2.
    cbn [fst snd] in *.
    replace (ret_pc (Z_to_bv 64 1087520)) with (Z_to_bv 64 1087520) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    clear ENV LS1 PRE1 CP2 m1.
    pose proof (cenv_silent LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -256) s bs OW m CEIL GLO' FBlo FBsp SPB FROK) as CSIL.
    assert (HWLs : forall bsx OWx, Forall (w_lib bsx OWx PL lo (bv_unsigned sp)) [(bv_unsigned sp + -256, bv_unsigned sp)]) by (intros bsx OWx; constructor; [left; cbn; lia| constructor]).
    assert (WOKs : forall OWx lsx, Forall (w_ok OWx LB lsx PL EA (bv_unsigned sp) []) [(bv_unsigned sp + -256, bv_unsigned sp)]) by (intros OWx lsx; constructor; [apply w_stack; cbn; lia| constructor]).
    destruct LEAF2 as (L2a & L2b & L2c & L2d). cbn [snd] in *.

    lazymatch type of ENV2 with cenv _ _ _ _ _ _ _ _ _ _ ?fr _ _ _ _ =>
    enough (AFTER : forall stK bsK mK OWK res ares z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z18 z20 z21 z23 z24 z25 z26 z28 z29 z30 z31,
       cenv LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -256) s bs OW m fr stK bsK mK OWK ->
       lib_state bsK mK OWK PL EA ->
       ref_at bsK OWK PL res ares -> wref PL res ->
       oref_at bsK OWK PL rm arm -> ref_at bsK OWK PL num anum -> ref_at bsK OWK PL dvs advs ->
       (res < NFIX + gx_pused (st_ctx bsK))%nat -> (num < NFIX + gx_pused (st_ctx bsK))%nat -> (dvs < NFIX + gx_pused (st_ctx bsK))%nat ->
       (1 <= bn_top (getbn dvs bsK))%nat -> nth (bn_top (getbn dvs bsK) - 1) (bn_buf (getbn dvs bsK)) 0 <> 0 ->
       implM bgusegs (interp (embed (div_rest res rm num dvs bsK))) stK
         (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA
                  (fun _ _ _ PL' a0' => PL' = PL /\ a0' = Z_to_bv 64 1))
        (MS (mkR z1 (Z_to_bv 64 (bv_unsigned sp + -256)) gp (Z_to_bv 64 RATP) z5 z6 z7 sp (Z_to_bv 64 ac) z10 z11 z12 z13 z14 z15 z16 z17
                 z18 (Z_to_bv 64 ares) z20 z21 (Z_to_bv 64 anum) z23 z24 z25 z26 (Z_to_bv 64 advs) z28 z29 z30 z31)
            F (Z_to_bv 64 0x109830) fc None mK (seg_rom bgusegs)))
    end.
    { pose proof (ref_at_stable _ _ _ _ _ _ _ RS2 HAnum) as HAnum2. pose proof (ref_at_stable _ _ _ _ _ _ _ RS2 HAdvs) as HAdvs2.
      pose proof (oref_at_stable _ _ _ _ _ _ _ RS2 HArm) as HArm2. pose proof (oref_at_stable _ _ _ _ _ _ _ RS2 HAdv) as HAdv2.
      assert (G2 : forall r, getbn r bs2 = getbn r bs) by (intros r; unfold getbn; rewrite L2a; reflexivity).
      destruct dv as [d|].
      -
        cbn [oref_at] in HAdv2. pose proof (WRdv d eq_refl) as WRd.
        pose proof (lib_state_h_parts _ _ _ _ _ _ LS2) as PARTS2.
        pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ (proj1 ENV2) PARTS2 FROK HAdv2 (proj1 WRd)) as (DA0 & DAC & _).
        assert (ADV : 0 < adv < 18446744073709551616) by (clear - DA0 DAC CEIL LO SPR B63 SPB; lia).
        rewrite bbind_ret.
        unfold MallocRep.wz. unfold implM. iprefix.
        zstep. if_cases KD; zify_cond KD. 2:{ exfalso. rewrite ?unsigned_lit in KD by lia. lia. }
        clear KD.
        ihere. to_implM.
        eapply AFTER; [exact ENV2 | exact LS2 | exact HAdv2 | exact WRd | exact HArm2 | exact HAnum2 | exact HAdvs2 | | | | |].
        + rewrite L2b. exact (LVv d eq_refl).
        + rewrite L2b. exact LVn.
        + rewrite L2b. exact LVd.
        + rewrite G2. exact HTOPD.
        + rewrite G2. exact HTOPNZ.
      -
        cbn [oref_at] in HAdv2. subst adv.
        unfold MallocRep.wz. unfold implM. iprefix.
        zstep. if_cases KD; zify_cond KD. { exfalso. rewrite ?unsigned_lit in KD by lia. lia. }
        clear KD.
        do 2 zstep.
        pose proof (lib_state_h_parts _ _ _ _ _ _ LS2) as (WFS2 & _).
        destruct (st_wf_get_pre bs2 WFS2) as (GP1 & GP2 & _).
        destruct (CPRE _ _ _ _ _ BN_CTX_GET_STACK ENV2 LS2 ltac:(unfold BN_CTX_GET_STACK; lia)) as (errv2 & PRE2).
        ihere. to_implM. unfold bbind at 1. cbn [bind tree_ops].
        eapply implM_embed_bind.
        { eapply BnLeaves.implM_embed_leaves; [apply (BN_CTX_get_leaves bs2 GP1 GP2)|].
          eapply (BN_CTX_get_walk HM) with (lo := lo) (B := B) (errv := errv2) (OW := OW2) (LB := LB) (PL := PL) (EA := EA) (ac := ac) (qc := qc);
            [exact PRE2 | reflexivity | exact EC | reflexivity]. }
        cbv beta. intros [res bs3] st3 ms3 [PO LEAF3]. apply BPC in PO.
        destruct PO as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & z14 & m3 & OW3 & PL3 & -> & CP3 & (EPL3 & _ & (ares & HAres & ->) & _)).
        subst PL3. specialize (CP3 eq_refl).
        destruct (CPOST _ _ _ _ _ _ _ _ _ ENV2 CP3) as (ENV3 & LS3).
        pose proof (cpost_refs LB PL EA lo B (bv_unsigned sp + -256) _ _ _ _ _ _ _ _ CP3) as RS3.
        cbn [fst snd] in *.
        replace (ret_pc (Z_to_bv 64 1087532)) with (Z_to_bv 64 1087532) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        clear PRE2 CP3.
        destruct LEAF3 as (L3a & L3b & L3c & L3d & _). cbn [fst snd] in *.
        unfold MallocRep.wz. unfold implM. iprefix.
        zstep.
        ihere. to_implM.
        eapply AFTER; [exact ENV3 | exact LS3 | exact HAres | rewrite L3a; apply wref_pool
                      | exact (oref_at_stable _ _ _ _ _ _ _ RS3 HArm2) | exact (ref_at_stable _ _ _ _ _ _ _ RS3 HAnum2) | exact (ref_at_stable _ _ _ _ _ _ _ RS3 HAdvs2) | | | | |].
        + rewrite L3a, L3b. unfold RPool. lia.
        + rewrite L3b, L2b. clear - LVn. lia.
        + rewrite L3b, L2b. clear - LVd. lia.
        + rewrite L3d by (rewrite L2b; unfold RPool; clear - LVd; lia). rewrite G2. exact HTOPD.
        + rewrite L3d by (rewrite L2b; unfold RPool; clear - LVd; lia). rewrite G2. exact HTOPNZ. }

    clear ENV2 LS2 RS2 L2a L2b L2c L2d HAdv HArm HAnum HAdvs HTOPD HTOPNZ LVn LVd LVv WRdv adv m2 OW2 st2 bs2 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14.
    intros stK bsK mK OWK res ares z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z18 z20 z21 z23 z24 z25 z26 z28 z29 z30 z31
           ENVK LSK HAresK WRres HArmK HAnumK HAdvsK LTres LTnum LTdvs HTOPD HTOPNZ.
    pose proof (proj1 WRres) as NROr.
    unfold div_rest.

    pose proof (lib_state_h_parts _ _ _ _ _ _ LSK) as (WFSK & _).
    destruct (st_wf_get_pre bsK WFSK) as (GPK1 & GPK2 & _).
    set (p := gx_pused (st_ctx bsK)) in *.
    unfold MallocRep.wz. unfold implM. iprefix.
    do 2 zstep.
    destruct (CPRE _ _ _ _ _ BN_CTX_GET_STACK ENVK LSK ltac:(unfold BN_CTX_GET_STACK; lia)) as (errv3 & PRE3).
    ihere. to_implM. unfold bbind at 1. cbn [bind tree_ops].
    eapply implM_embed_bind.
    { eapply BnLeaves.implM_embed_leaves; [apply (BN_CTX_get_leaves bsK GPK1 GPK2)|].
      eapply (BN_CTX_get_walk HM) with (lo := lo) (B := B) (errv := errv3) (OW := OWK) (LB := LB) (PL := PL) (EA := EA) (ac := ac) (qc := qc);
        [exact PRE3 | reflexivity | exact EC | reflexivity]. }
    cbv beta. intros [tmp bs3] st3 ms3 [PO LEAF3]. apply BPC in PO.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m3 & OW3 & PL3 & -> & CP3 & (EPL3 & _ & (atmp & HAtmp & ->) & _)).
    subst PL3. specialize (CP3 eq_refl).
    destruct (CPOST _ _ _ _ _ _ _ _ _ ENVK CP3) as (ENV3 & LS3).
    pose proof (cpost_refs LB PL EA lo B (bv_unsigned sp + -256) _ _ _ _ _ _ _ _ CP3) as RS3.
    cbn [fst snd] in *.
    replace (ret_pc (Z_to_bv 64 1087544)) with (Z_to_bv 64 1087544) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    clear PRE3 CP3 GPK1 GPK2.

    unfold MallocRep.wz. unfold implM. iprefix.
    do 3 zstep.
    pose proof ENV3 as ENV3'. pose proof LS3 as LS3'.

    pose proof (lib_state_h_parts _ _ _ _ _ _ LS3') as (WFS3 & _).
    destruct (st_wf_get_pre bs3 WFS3) as (GP31 & GP32 & _).
    destruct (CPRE _ _ _ _ _ BN_CTX_GET_STACK ENV3' LS3' ltac:(unfold BN_CTX_GET_STACK; lia)) as (errv4 & PRE4).
    ihere. to_implM. unfold bbind at 1. cbn [bind tree_ops].
    eapply implM_embed_bind.
    { eapply BnLeaves.implM_embed_leaves; [apply (BN_CTX_get_leaves bs3 GP31 GP32)|].
      eapply (BN_CTX_get_walk HM) with (lo := lo) (B := B) (errv := errv4) (OW := OW3) (LB := LB) (PL := PL) (EA := EA) (ac := ac) (qc := qc);
        [exact PRE4 | reflexivity | exact EC | reflexivity]. }
    cbv beta. intros [snum bs4] st4 ms4 [PO LEAF4]. apply BPC in PO.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m4 & OW4 & PL4 & -> & CP4 & (EPL4 & _ & (asnum & HAsnum & ->) & _)).
    subst PL4. specialize (CP4 eq_refl).
    destruct (CPOST _ _ _ _ _ _ _ _ _ ENV3' CP4) as (ENV4 & LS4).
    pose proof (cpost_refs LB PL EA lo B (bv_unsigned sp + -256) _ _ _ _ _ _ _ _ CP4) as RS4.
    cbn [fst snd] in *.
    replace (ret_pc (Z_to_bv 64 1087556)) with (Z_to_bv 64 1087556) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    clear PRE4 CP4 GP31 GP32.
    env_open ENV4. unfold MallocRep.wz. unfold implM. iprefix.
    step. step. do 2 zstep.
    env_close CSIL HWLs WOKs ENV4 LS4 ENV4' LS4'.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS4') as (WFS4 & _).
    destruct (st_wf_get_pre bs4 WFS4) as (GP41 & GP42 & _).
    destruct (CPRE _ _ _ _ _ BN_CTX_GET_STACK ENV4' LS4' ltac:(unfold BN_CTX_GET_STACK; lia)) as (errv5 & PRE5).
    ihere. to_implM. unfold bbind at 1. cbn [bind tree_ops].
    eapply implM_embed_bind.
    { eapply BnLeaves.implM_embed_leaves; [apply (BN_CTX_get_leaves bs4 GP41 GP42)|].
      eapply (BN_CTX_get_walk HM) with (lo := lo) (B := B) (errv := errv5) (OW := OW4) (LB := LB) (PL := PL) (EA := EA) (ac := ac) (qc := qc);
        [exact PRE5 | reflexivity | exact EC | reflexivity]. }
    cbv beta. intros [sdiv bs5] st5 ms5 [PO LEAF5]. apply BPC in PO.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m5 & OW5 & PL5 & -> & CP5 & (EPL5 & _ & (asdiv & HAsdiv & ->) & _)).
    subst PL5. specialize (CP5 eq_refl).
    destruct (CPOST _ _ _ _ _ _ _ _ _ ENV4' CP5) as (ENV5 & LS5).
    pose proof (cpost_refs LB PL EA lo B (bv_unsigned sp + -256) _ _ _ _ _ _ _ _ CP5) as RS5.
    cbn [fst snd] in *.
    replace (ret_pc (Z_to_bv 64 1087572)) with (Z_to_bv 64 1087572) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    clear PRE5 CP5 GP41 GP42.

    destruct LEAF3 as (L3a & L3b & _ & L3d & _). destruct LEAF4 as (L4a & L4b & _ & L4d & _). destruct LEAF5 as (L5a & L5b & _ & L5d & _).
    cbn [fst snd] in *. fold p in L3a, L3b, L3d.
    rewrite L3b in L4a, L4d. rewrite L4b, L3b in L5a, L5d.
    assert (LOWget : forall r, (r < NFIX + p)%nat -> getbn r bs5 = getbn r bsK).
    { intros r Hr. rewrite L5d by (unfold RPool; clear - Hr; lia). rewrite L4d by (unfold RPool; clear - Hr; lia). apply L3d. unfold RPool. clear - Hr. lia. }
    pose proof (ref_at_stable _ _ _ _ _ _ _ RS5 (ref_at_stable _ _ _ _ _ _ _ RS4 (ref_at_stable _ _ _ _ _ _ _ RS3 HAresK))) as HAdv5.
    pose proof (oref_at_stable _ _ _ _ _ _ _ RS5 (oref_at_stable _ _ _ _ _ _ _ RS4 (oref_at_stable _ _ _ _ _ _ _ RS3 HArmK))) as HArm5.
    pose proof (ref_at_stable _ _ _ _ _ _ _ RS5 (ref_at_stable _ _ _ _ _ _ _ RS4 (ref_at_stable _ _ _ _ _ _ _ RS3 HAnumK))) as HAnum5.
    pose proof (ref_at_stable _ _ _ _ _ _ _ RS5 (ref_at_stable _ _ _ _ _ _ _ RS4 (ref_at_stable _ _ _ _ _ _ _ RS3 HAdvsK))) as HAdvs5.
    pose proof (ref_at_stable _ _ _ _ _ _ _ RS5 (ref_at_stable _ _ _ _ _ _ _ RS4 HAtmp)) as HAtmp5. pose proof (ref_at_stable _ _ _ _ _ _ _ RS5 HAsnum) as HAsnum5.
    assert (NEts : tmp <> snum) by (rewrite L3a, L4a; unfold RPool; clear; lia).
    assert (NEtd : tmp <> sdiv) by (rewrite L3a, L5a; unfold RPool; clear; lia).
    assert (NEsd : snum <> sdiv) by (rewrite L4a, L5a; unfold RPool; clear; lia).
    assert (NEvt : res <> tmp) by (rewrite L3a; unfold RPool; clear - LTres; lia).
    assert (NEvs : res <> snum) by (rewrite L4a; unfold RPool; clear - LTres; lia).
    assert (NEvd : res <> sdiv) by (rewrite L5a; unfold RPool; clear - LTres; lia).
    assert (NEnt : num <> tmp) by (rewrite L3a; unfold RPool; clear - LTnum; lia).
    assert (NEns : num <> snum) by (rewrite L4a; unfold RPool; clear - LTnum; lia).
    assert (NEnd : num <> sdiv) by (rewrite L5a; unfold RPool; clear - LTnum; lia).
    assert (NEdt : dvs <> tmp) by (rewrite L3a; unfold RPool; clear - LTdvs; lia).
    assert (NEds : dvs <> snum) by (rewrite L4a; unfold RPool; clear - LTdvs; lia).
    assert (NEdd : dvs <> sdiv) by (rewrite L5a; unfold RPool; clear - LTdvs; lia).
    assert (HPt : hpl PL tmp) by (rewrite L3a; apply hpl_pool).
    assert (HPs : hpl PL snum) by (rewrite L4a; apply hpl_pool).
    assert (HPd : hpl PL sdiv) by (rewrite L5a; apply hpl_pool).
    pose proof (proj1 HPt) as NROt. pose proof (proj1 HPs) as NROs. pose proof (proj1 HPd) as NROsd.
    assert (HTOPD5 : (1 <= bn_top (getbn dvs bs5))%nat) by (rewrite (LOWget dvs LTdvs); exact HTOPD).
    assert (HTOPNZ5 : nth (bn_top (getbn dvs bs5) - 1) (bn_buf (getbn dvs bs5)) 0 <> 0) by (rewrite (LOWget dvs LTdvs); exact HTOPNZ).
    clear L3a L3b L3d L4a L4b L4d L5a L5b L5d RS3 RS4 RS5 HAtmp HAsnum ENV3 LS3 ENV3' LS3' ENV4 LS4 ENV4' LS4' WFSK WFS3 WFS4.
    clear HAresK HArmK HAnumK HAdvsK ENVK LSK LOWget HTOPD HTOPNZ LTres LTnum LTdvs p.

    repeat match goal with H : _ <> _ |- _ => apply hide_intro in H end.

    pose proof (lib_state_h_parts _ _ _ _ _ _ LS5) as PARTS5; pose proof PARTS5 as (WFS5 & PWF5 & IDS5 & PLB5 & ERRB5).
    pose proof (ref_at_hrange _ _ _ _ _ _ _ _ _ (proj1 ENV5) PARTS5 HAsdiv HPd) as (DA0 & DAC & _ & _).
    unfold MallocRep.wz. unfold implM. iprefix.
    zstep. if_cases KD; zify_cond KD. { exfalso. rewrite ?unsigned_lit in KD by lia. lia. }
    clear KD DA0 DAC.
    do 3 zstep.

    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS5 HAsdiv) as HVsd5. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS5 HAdvs5) as HVdvs5.
    pose proof (st_wf_ok sdiv bs5 WFS5 HVsd5 NROsd) as (_ & OKsd2 & _). pose proof (st_wf_ok dvs bs5 WFS5 HVdvs5 NROd) as (OKdv1 & OKdv2 & OKdv3 & _).
    destruct (CPRE _ _ _ _ _ BN_COPY_STACK ENV5 LS5 ltac:(unfold BN_COPY_STACK, BN_EXPAND2_STACK; lia)) as (errv6 & PRE6).
    ihere. to_implM. unfold div_core. unfold bbind at 1. cbn [bind tree_ops].
    eapply implM_embed_bind.
    { eapply BnLeaves.implM_embed_leaves; [apply (BN_copy_leaves sdiv dvs bs5 (not_eq_sym NEdd) HVsd5 OKsd2 OKdv2)|].
      eapply (BN_copy_walk HM HF) with (lo := lo) (B := B) (errv := errv6) (OW := OW5) (LB := LB) (PL := PL) (EA := EA) (rx := sdiv) (ry := dvs) (ax := asdiv) (ay := advs);
        [exact PRE6 | reflexivity | exact HAsdiv | exact HAdvs5 | exact (hpl_wref PL sdiv HPd) | exact NROd | reflexivity | reflexivity]. }
    cbv beta. intros [u6 bs6] st6 ms6 [PO LEAF6]. apply BPC in PO.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m6 & OW6 & PL6 & -> & CP6 & (EPL6 & -> & _)).
    subst PL6. specialize (CP6 eq_refl).
    destruct (CPOST _ _ _ _ _ _ _ _ _ ENV5 CP6) as (ENV6 & LS6).
    pose proof (cpost_refs LB PL EA lo B (bv_unsigned sp + -256) _ _ _ _ _ _ _ _ CP6) as RS6.
    cbn [fst snd] in *.
    replace (ret_pc (Z_to_bv 64 1087588)) with (Z_to_bv 64 1087588) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    clear PRE6 CP6.

    destruct LEAF6 as (C6a & C6b & C6c & C6d & C6e & _). cbn [snd] in *.
    pose proof (ref_at_stable _ _ _ _ _ _ _ RS6 HAdv5) as HAdv6. pose proof (oref_at_stable _ _ _ _ _ _ _ RS6 HArm5) as HArm6.
    pose proof (ref_at_stable _ _ _ _ _ _ _ RS6 HAnum5) as HAnum6. pose proof (ref_at_stable _ _ _ _ _ _ _ RS6 HAdvs5) as HAdvs6.
    pose proof (ref_at_stable _ _ _ _ _ _ _ RS6 HAtmp5) as HAtmp6. pose proof (ref_at_stable _ _ _ _ _ _ _ RS6 HAsnum5) as HAsnum6.
    pose proof (ref_at_stable _ _ _ _ _ _ _ RS6 HAsdiv) as HAsdiv6.
    set (bd := getbn dvs bs5) in *. set (dn := bn_top bd) in *.
    clear RS6 HAdv5 HArm5 HAnum5 HAdvs5 HAtmp5 HAsnum5 HAsdiv ENV5 LS5 PARTS5 WFS5 PWF5 IDS5 PLB5 ERRB5 HVsd5 HVdvs5 OKsd2 C6a.
    pose proof (RH_nodup_l _ _ _ _ (proj1 ENV6)) as ND6.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS6) as PARTS6; pose proof PARTS6 as (WFS6 & PWF6 & IDS6 & PLB6 & ERRB6).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS6 HAsdiv6) as HVsd6.
    destruct (lib_state_open [] bs6 m6 OW6 PL EA sdiv asdiv LS6 ND6 HAsdiv6 ltac:(intros []) NROsd) as ((Dsd & BNsd & ARRsd) & (OKs1 & OKs2 & OKs3 & OKs4) & LSH6).
    set (b6 := getbn sdiv bs6) in *.
    destruct (bn_arr_facts_w bs6 OW6 PL EA (bv_unsigned sp) B st6 LB m6 sdiv Dsd (proj1 ENV6) PARTS6 FROK HVsd6 (hpl_wref PL sdiv HPd) ARRsd) as (Usd & LENsd & Dsd0 & DsdC & DsdI & DSEPsd).
    fold b6 in Usd, LENsd, DsdC, DsdI, DSEPsd.
    pose proof (DSEPsd sdiv asdiv HAsdiv6) as SEPsd. clear DSEPsd.
    pose proof (ref_at_hrange _ _ _ _ _ _ _ _ _ (proj1 ENV6) PARTS6 HAsdiv6 HPd) as (SDA0 & SDAC & SDAI & (qsd & Asd & nsd & Hinsd & Rsd1 & Rsd2)).
    assert (HDsd : exists psd, bn_d b6 = Some psd /\ In (psd, Dsd, 8 * Z.of_nat (bn_dmax b6)) OW6).
    { destruct (bn_d b6) as [psd|] eqn:Edsd0; [exists psd; split; [reflexivity|]; unfold bn_arr in ARRsd; rewrite Edsd0 in ARRsd; exact (proj1 ARRsd)|].
      exfalso. destruct (bn_arr_null PL sdiv m6 OW6 Dsd b6 PWF6 (hpl_wref PL sdiv HPd) Edsd0 ARRsd) as [_ E]. unfold bn_dmax in C6e. rewrite E in C6e. cbn in C6e. fold dn in C6e. clear - C6e HTOPD5. lia. }
    destruct HDsd as (psd & Edsd & Hinpsd).
    unfold bn_cells in BNsd. rewrite C6b, C6c in BNsd. fold dn in BNsd. unfold BG_DMAX in OKs3, OKdv3.
    env_open ENV6.
    match goal with MUx : munch _ m6 m6 |- _ => clear MUx end. match goal with WMx : wmono _ m6 m6 |- _ => clear WMx end.
    pose proof (munch_refl [(bv_unsigned sp - 272, bv_unsigned sp); (asdiv, asdiv + 24); (Dsd, Dsd + 8 * Z.of_nat (bn_dmax b6))]%Z m6) as MU6.
    pose proof (wmono_refl bgusegs m6) as WM6.
    unfold MallocRep.wz in *. unfold implM. iprefix.
    zstep. if_cases KD; zify_cond KD. { exfalso. rewrite ?unsigned_lit in KD by lia. lia. }
    clear KD.
    pose proof (ref_at_ualign _ _ _ _ _ _ _ _ _ (proj1 ENV6) PARTS6 HAsdiv6 (proj1 HPd)) as (SDP & SD8).
    pose proof (block_ualign _ _ _ _ _ _ _ (proj1 ENV6) Hinpsd) as (DSP & DS8).
    zstep. rewrite (land7 asdiv) by exact SD8.
    chk ltac:(fun C => clear - C; lia).
    zstep.
    step. rewrite (sx32_small (Z.of_nat dn)) by (unfold dn, bn_dmax in *; lia).
    zstep. rewrite (bk_swrap32_small (Z.of_nat dn + -1)) by lia.
    zstep. rewrite lts_signed by lia. if_cases KO; zify_cond KO. { exfalso. clear - KO. lia. } clear KO.
    step. do 2 zstep.
    replace (Dsd + (Z.of_nat dn + -1) ≪ 3) with (Dsd + 8 * (Z.of_nat dn - 1)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    do 2 zstep. rewrite ?land64_small by (unfold bn_dmax in *; lia).
    replace (0 <? Dsd) with true by (symmetry; apply Z.ltb_lt; exact DSP).
    replace (Dsd + 8 * (Z.of_nat dn - 1) <? 1) with false by (symmetry; apply Z.ltb_ge; clear - DSP HTOPD5; lia).
    cbn [Z.b2z].
    chk ltac:(fun C => clear - C; lia).
    do 4 zstep.
    rewrite (lxor_signbit63' (Z.of_nat dn + -1)) by (clear - HTOPD5 OKs3 C6e OKs2; unfold bn_dmax in *; lia).
    replace (Z.of_nat dn + -1 + 9223372036854775808 <? 9223372036854775808) with false by (symmetry; apply Z.ltb_ge; clear - HTOPD5; lia).
    replace (Dsd + 8 * (Z.of_nat dn - 1) <? Dsd) with false by (symmetry; apply Z.ltb_ge; clear - HTOPD5; lia).
    cbn [Z.b2z Z.lxor].
    chk ltac:(fun C => clear - C; lia).
    chk ltac:(fun C => rewrite ?unsigned_lit in C by lia; lia).
    zstep. rewrite (land7 (Dsd + 8 * (Z.of_nat dn - 1))) by (clear - DS8; Z.div_mod_to_equations; lia).
    chk ltac:(fun C => clear - C; lia).

    set (dtop := nth (dn - 1) (bn_buf bd) 0) in *.
    assert (Edtop : nth (dn - 1) (bn_buf b6) 0 = dtop).
    { unfold dtop. rewrite <- (firstn_skipn dn (bn_buf b6)), <- (firstn_skipn dn (bn_buf bd)), C6d.
      rewrite !app_nth1 by (rewrite length_firstn; unfold bn_dmax in *; lia). reflexivity. }
    assert (Rdtop : 0 < dtop < 18446744073709551616).
    { assert (L : limb dtop) by (apply limbs_nth; exact OKdv1). unfold limb in L. rewrite BW_lit in L. pose proof (hide_elim _ HTOPNZ5) as NZ. fold dtop in NZ. clear - L NZ. lia. }
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      destruct (proj1 (limbarr_limbs_at bgusegs mx Dsd (bn_buf b6)) Usd) as (LAsd & WRsd) end.
    assert (Ntop : nth_error (bn_buf b6) (dn - 1) = Some dtop) by (rewrite <- Edtop; apply nth_error_nth'; unfold bn_dmax in *; lia).
    let ad := cur_mem_addr in
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        pose proof (limbs_at_read_nth bgusegs mx Dsd (bn_buf b6) (dn - 1) dtop ad LAsd Ntop ltac:(unfold wa; f_equal; lia)) as RD end.
    zstep. clear RD.
    zstep.
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -256)) = bv_unsigned sp + -256) by (apply unsigned_lit; lia).
    assert (Edt : bv_unsigned (Z_to_bv 64 dtop) = dtop) by (apply unsigned_lit; lia).
    eapply evt_cut.
    { match goal with STx : stk _ m6 _ _, MIx : mem_inv _ m6 |- _ =>
        eapply BN_num_bits_word_uspec with (lo := lo) (m := m6); [rewrite ESP; exact STx | rewrite ESP; lia | exact MIx] end. }
    intros ms' PO. unfold nbw_upost in PO.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m8 & E & MUc & WMc & MIc & STc).
    subst ms'. rewrite ESP, Edt in *.
    replace (ret_pc (Z_to_bv 64 1087680)) with (Z_to_bv 64 1087680) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (LAsd8 : limbs_at bgusegs m8 Dsd (bn_buf b6)).
    { eapply limbs_at_transport; [exact LAsd | exact MUc |]. cbn [disjoint_from]. fold (bn_dmax b6). split; [|exact I]. lia. }
    clear LAsd WRsd.
    match goal with STx : stk _ m6 _ _ |- _ => clear STx end.
    transport_after_call bgusegs m6 m8 MUc WMc.
    clear MUc WMc. match goal with MIx : mem_inv _ m6 |- _ => clear MIx end.

    set (nb := num_bits_word dtop) in *.
    assert (NB : 1 <= nb <= 64).
    { destruct (num_bits_word_spec dtop ltac:(lia)) as (B1 & _). pose proof (num_bits_word_le dtop 64 ltac:(lia) ltac:(change (2 ^ 64) with 18446744073709551616; lia)). fold nb in B1, H. lia. }
    set (af := firstn dn (bn_buf b6)).
    assert (Laf : length af = dn) by (unfold af; apply firstn_length_le; unfold bn_dmax in *; lia).
    assert (LAaf : limbs_at bgusegs m8 Dsd af).
    { rewrite <- (firstn_skipn dn (bn_buf b6)) in LAsd8. apply limbs_at_app in LAsd8. exact (proj1 LAsd8). }
    assert (LArest : limbs_at bgusegs m8 (Dsd + 8 * Z.of_nat dn) (skipn dn (bn_buf b6))).
    { rewrite <- (firstn_skipn dn (bn_buf b6)) in LAsd8. apply limbs_at_app in LAsd8. destruct LAsd8 as [_ X]. fold af in X. rewrite Laf in X. exact X. }
    destruct (proj1 (limbarr_limbs_at bgusegs m8 Dsd (bn_buf b6)) Usd) as (_ & WRsd8).
    replace (Z_to_bv 64 (Z.of_nat dn)) with (Z_to_bv 64 (Z.of_nat (length af))) by (rewrite Laf; reflexivity).
    lazymatch type of FRe with rw_cells _ _ _ ?fr =>
    eapply la_ublock with (m := m8) (D := Dsd) (SP := bv_unsigned sp) (lo := lo) (a := af) (lb := 64 - nb) (FS := 256) (FB := bv_unsigned sp + -256) (FCELLS := fr) (nb := nb)
    end.
    { reflexivity. }
    { lia. }
    { lia. }
    { rewrite Laf. left. unfold bn_dmax in *. lia. }
    { exact NB. }
    { reflexivity. }
    { rewrite Laf. lia. }
    { unfold af. apply limbs_firstn. exact OKs1. }
    { exact LAaf. }
    { rewrite Laf. apply (wr_at_sub bgusegs m8 Dsd (8 * Z.of_nat (length (bn_buf b6))) 0 (8 * Z.of_nat dn)) in WRsd8; [rewrite Z.add_0_r in WRsd8; exact WRsd8 | lia | lia | unfold bn_dmax in *; lia]. }
    { exact FRe. }
    { exact STc. }
    { exact MIc. }
    intros m9 w5 w6 w10 w11 w13 w14 w15 w16 w17 w18 HRES FR9 ST9 MI9 MU9 WM9. rewrite Laf in MU9.
    set (sh := 64 - nb) in *.
    set (resl := fst (lshift_limbs af sh 0)) in *.
    assert (Lres : length resl = dn) by (unfold resl; rewrite lshift_limbs_len; exact Laf).

    assert (DNM : Z.of_nat dn <= Z.of_nat (bn_dmax b6)) by (clear - C6e; fold dn in C6e; lia).
    assert (DN1 : 1 <= Z.of_nat dn) by (clear - HTOPD5; lia).
    assert (ERRD : 3346164 + 4 <= Dsd \/ Dsd + 8 * Z.of_nat (bn_dmax b6) <= 3346164) by (clear - DsdI DNM DN1; lia).
    assert (SDLIN : asdiv + 24 <= bv_unsigned sp - 256) by (clear - SDAC CEIL LO; lia).
    assert (DSLIN : Dsd + 8 * Z.of_nat (bn_dmax b6) <= bv_unsigned sp - 256) by (clear - DsdC CEIL LO; lia).
    assert (ERLIN : 3346164 + 4 <= bv_unsigned sp - 256) by (clear - GLO LO; lia).
    repeat match goal with H : _ \/ _ |- _ => apply hide_intro in H end.
    assert (DJ9 : forall A k, (A + k <= Dsd \/ Dsd + 8 * Z.of_nat (bn_dmax b6) <= A) -> A + k <= bv_unsigned sp - 256 ->
              disjoint_from [(Dsd, Dsd + 8 * Z.of_nat dn); (bv_unsigned sp - 256, bv_unsigned sp)] A k).
    { intros A k H1 H2. cbn [disjoint_from]. clear - H1 H2 DNM. lia. }
    eapply (rw_cells_transport bgusegs _ m8 m9) in BNsd; [| exact MU9 | exact WM9 | apply DJ9; cbn [cells_size csize Nat.add]; [apply hide_elim in SEPsd; clear - SEPsd; lia| clear - SDLIN; lia]].
    eapply (rw_cells_transport bgusegs _ m8 m9) in ERRe; [| exact MU9 | exact WM9 | apply DJ9; cbn [cells_size csize Nat.add]; [apply hide_elim in ERRD; clear - ERRD; lia| clear - ERLIN; lia]].
    assert (LArest9 : limbs_at bgusegs m9 (Dsd + 8 * Z.of_nat dn) (skipn dn (bn_buf b6))).
    { eapply limbs_at_transport; [exact LArest | exact MU9 |]. cbn [disjoint_from]. rewrite length_skipn. unfold bn_dmax in *. clear - DNM DSLIN. unfold bn_dmax in *. lia. }
    set (nbuf := splice (bn_buf b6) 0 resl).
    assert (Lnbuf : length nbuf = bn_dmax b6) by (unfold nbuf, bn_dmax in *; rewrite splice_length by (clear - Lres DNM; unfold bn_dmax in *; lia); reflexivity).
    assert (U9 : u64arr bgusegs m9 Dsd (wlimbs nbuf)).
    { apply limbarr_limbs_at. split.
      - unfold nbuf, splice. change (firstn 0 (bn_buf b6)) with (@nil Z). change (0 + length resl)%nat with (length resl).
        change ([] ++ resl ++ skipn (length resl) (bn_buf b6)) with (resl ++ skipn (length resl) (bn_buf b6)).
        apply limbs_at_app. split; [exact HRES|]. rewrite Lres. exact LArest9.
      - rewrite Lnbuf. eapply wr_at_transport; [exact WRsd8 | exact WM9]. }
    assert (MU6' : munch [(bv_unsigned sp - 272, bv_unsigned sp); (asdiv, asdiv + 24); (Dsd, Dsd + 8 * Z.of_nat (bn_dmax b6))]%Z m6 m9).
    { eapply munch_trans; [exact MU6|]. eapply munch_weaken; [|exact MU9]. unfold sub_fp. intros xx Hxx. cbn [outside] in *. clear - Hxx DNM. lia. }
    assert (WM6' : wmono bgusegs m6 m9) by (eapply wmono_trans; eauto).
    assert (LENnb : Z.of_nat (length (wlimbs nbuf)) = Z.of_nat (bn_dmax b6)) by (rewrite wlimbs_len, Lnbuf; reflexivity).
    clear MU6 WM6 MU9 WM9 Usd LENsd LAsd8 LAaf LArest LArest9 HRES WRsd8 DJ9 FRe STc MIc.

    pose proof (munch_refl [(asdiv, asdiv + 24); (bv_unsigned sp - 256, bv_unsigned sp)]%Z m9) as MUa. pose proof (wmono_refl bgusegs m9) as WMa.
    apply hide_intro in ERRe. apply hide_intro in U9.
    step. step. zstep. step. zstep.

    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m10 end.
    apply hide_elim in ERRe. apply hide_elim in U9.
    eapply (rw_cells_transport bgusegs _ m9 m10) in ERRe; [| exact MUa | exact WMa | cbn [disjoint_from cells_size csize Nat.add]; split; [apply hide_elim in SDAI; clear - SDAI; lia| split; [clear - ERLIN; lia | exact I]]].
    eapply (u64arr_transport bgusegs _ m9 m10) in U9; [| exact MUa | exact WMa | cbn [disjoint_from]; rewrite LENnb; split; [apply hide_elim in SEPsd; clear - SEPsd; lia| split; [clear - DSLIN; lia | exact I]]].
    clear MUa WMa.
    ihere. to_implM. unfold bbind at 1. cbn [bind tree_ops]. rewrite la_run. cbn [tbind fst snd]. rewrite bbind_get_set.
    fold b6. rewrite C6b. fold dn. rewrite Edtop. fold nb. fold sh. fold af. fold resl. fold nbuf.
    rewrite (getbn_setbn_same sdiv _ bs6 HVsd6), setbn_setbn_same.
    set (sd3 := bn_with_neg (bn_with_buf b6 nbuf) false).
    unfold bbind at 1. cbn [bind tree_ops].
    assert (HWL6 : Forall (w_lib bs6 OW6 PL lo (bv_unsigned sp)) [(bv_unsigned sp - 272, bv_unsigned sp); (asdiv, asdiv + 24); (Dsd, Dsd + 8 * Z.of_nat (bn_dmax b6))]).
    { constructor; [left; cbn; lia|]. constructor; [right; left; exists (qsd, Asd, nsd); cbn; auto|].
      constructor; [right; left; exists (psd, Dsd, 8 * Z.of_nat (bn_dmax b6)); cbn; split; [exact Hinpsd| lia]| constructor]. }
    assert (WOK6 : Forall (w_ok OW6 LB bs6 PL EA (bv_unsigned sp) [sdiv]) [(bv_unsigned sp - 272, bv_unsigned sp); (asdiv, asdiv + 24); (Dsd, Dsd + 8 * Z.of_nat (bn_dmax b6))]).
    { constructor; [apply w_stack; cbn; lia|]. constructor; [eapply (w_struct OW6 LB bs6 PL EA (bv_unsigned sp) false [sdiv] _ sdiv asdiv); [left; reflexivity| exact HAsdiv6| exact NROsd| cbn; lia| cbn; lia]|].
      constructor; [eapply (w_limbs OW6 LB bs6 PL EA (bv_unsigned sp) false [sdiv] _ sdiv psd Dsd); [left; reflexivity| exact HVsd6| exact Edsd| exact Hinpsd| cbn [fst snd]; fold b6; lia| cbn [fst snd]; fold b6; lia]| constructor]. }
    pose proof (BnSpecs2.left_align_value af ltac:(unfold af; apply limbs_firstn; exact OKs1) ltac:(rewrite Laf; lia)) as LAV.
    rewrite Laf in LAV.
    assert (Eaft : nth (dn - 1) af 0 = dtop) by (unfold af; rewrite nth_firstn; destruct (Nat.ltb_spec (dn - 1) dn); [exact Edtop | lia]).
    rewrite Eaft in LAV. specialize (LAV ltac:(lia)). cbv zeta in LAV. fold nb in LAV. fold sh in LAV. fold resl in LAV.
    destruct LAV as (SH & LRES & _ & VRES & D0N).
    assert (LS7 : lib_state (setbn sdiv sd3 bs6) m10 OW6 PL EA).
    { unfold lib_state. eapply (lib_state_close [] bs6 m10 OW6 PL EA sdiv asdiv); [| exact ND6| exact HAsdiv6| exact NROsd| | |].
      - match goal with HEAPx : RHEAP st6 _ m6 |- _ => exact (lib_state_frame st6 LB _ _ [sdiv] bs6 m6 m10 OW6 PL EA _ HEAPx LSH6 MU6' WM6' FROK WOK6) end.
      - exists Dsd. split.
        + unfold bn_cells, sd3, bn_dmax. cbn [bn_with_neg bn_with_buf bn_top bn_buf bn_neg bn_flags Z.b2z]. rewrite Lnbuf, C6b. fold dn. exact BNsd.
        + unfold bn_arr, sd3, bn_dmax. cbn [bn_with_neg bn_with_buf bn_d bn_buf]. rewrite Edsd, Lnbuf. split; [exact Hinpsd| exact U9].
      - unfold bg_ok, sd3, bn_dmax. cbn [bn_with_neg bn_with_buf bn_buf bn_top bn_flags]. rewrite Lnbuf. unfold BG_DMAX.
        split; [unfold nbuf; apply splice_limbs; [exact OKs1| exact LRES]|]. split; [exact OKs2|]. split; [lia| exact OKs4].
      - apply ids_ok_setbn_same; [exact IDS6| exact HVsd6|]. unfold bn_blocks, sd3, bn_dmax. cbn [bn_with_neg bn_with_buf bn_d bn_buf]. rewrite Lnbuf. reflexivity. }
    lazymatch type of ENV6 with cenv ?a ?b ?c ?d ?e ?f ?g ?h ?i ?j _ _ _ _ _ =>
      lazymatch goal with FRx : rw_cells _ m10 (bv_unsigned sp + -256) ?fr' |- _ =>
        assert (ENV7 : cenv a b c d e f g h i j fr' st6 (setbn sdiv sd3 bs6) m10 OW6) end end.
    { apply cenv_setbn.
      match goal with FRx : rw_cells _ m10 (bv_unsigned sp + -256) ?fr', STx : stk _ m10 _ _, MIx : mem_inv _ m10, ERRx : rw_cells _ m10 3346164 _ |- _ =>
        eapply (CSIL _ fr'); [exact ENV6 | exact LS6 | exact MU6' | exact WM6' | exact HWL6 | exact STx | unfold LX_ERRNO, RATP; exact ERRx | exact MIx | exact FRx | cbn; lia] end. }
    set (bs7 := setbn sdiv sd3 bs6) in *.
    assert (HAsnum7 : ref_at bs7 OW6 PL snum asnum) by (apply ref_at_setbn; exact HAsnum6).
    assert (HAnum7 : ref_at bs7 OW6 PL num anum) by (apply ref_at_setbn; exact HAnum6).
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS7) as (WFS7 & _).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS7 HAsnum7) as HVsn7. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS7 HAnum7) as HVnum7.
    pose proof (st_wf_ok snum bs7 WFS7 HVsn7 NROs) as (_ & OKsn2 & _). pose proof (st_wf_ok num bs7 WFS7 HVnum7 NROn) as (OKn1 & OKn2 & OKn3 & _).
    destruct (CPRE _ _ _ _ _ BN_LSHIFT_STACK ENV7 LS7 ltac:(unfold BN_LSHIFT_STACK, BN_WEXPAND_STACK, BN_EXPAND2_STACK; lia)) as (errv7 & PRE7).
    eapply implM_embed_bind.
    { eapply BnLeaves.implM_embed_leaves; [apply (bn_lshift_leaves snum num sh bs7 (not_eq_sym NEns) SH HVsn7 OKsn2 OKn2)|].
      eapply (bn_lshift_fixed_top_walk HM HF) with (lo := lo) (B := B) (errv := errv7) (OW := OW6) (LB := LB) (PL := PL) (EA := EA) (rr := snum) (rx := num) (R := asnum) (X := anum) (n := sh);
        [exact PRE7 | reflexivity | exact HAsnum7 | exact HPs | exact HAnum7 | exact NROn | reflexivity | reflexivity | reflexivity | clear - SH; lia]. }
    cbv beta. intros [u8 bs8] st8 ms8 [PO LEAF8]. apply BPC in PO.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m11 & OW8 & PL8 & -> & CP8 & (EPL8 & -> & _)).
    subst PL8. specialize (CP8 eq_refl).
    destruct (CPOST _ _ _ _ _ _ _ _ _ ENV7 CP8) as (ENV8 & LS8).
    pose proof (cpost_refs LB PL EA lo B (bv_unsigned sp + -256) _ _ _ _ _ _ _ _ CP8) as RS8.
    cbn [fst snd] in *.
    replace (ret_pc (Z_to_bv 64 1087820)) with (Z_to_bv 64 1087820) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    clear PRE7 CP8.

    destruct LEAF8 as (L8a & L8b & L8c & L8d & L8e & _). cbn [snd] in *.
    set (bnum := getbn num bs7) in *. set (tn := bn_top bnum) in *.
    assert (Esd8 : getbn sdiv bs8 = sd3) by (rewrite L8a by exact NEsd; unfold bs7; apply getbn_setbn_same; exact HVsd6).
    pose proof (ref_at_stable _ _ _ _ _ _ _ RS8 (proj2 (ref_at_setbn bs6 OW6 PL sdiv sd3 _ _) HAdv6)) as HAdv8.
    pose proof (oref_at_stable _ _ _ _ _ _ _ RS8 (oref_at_setbn bs6 OW6 PL sdiv sd3 _ _ HArm6)) as HArm8.
    pose proof (ref_at_stable _ _ _ _ _ _ _ RS8 HAnum7) as HAnum8.
    pose proof (ref_at_stable _ _ _ _ _ _ _ RS8 (proj2 (ref_at_setbn bs6 OW6 PL sdiv sd3 _ _) HAdvs6)) as HAdvs8.
    pose proof (ref_at_stable _ _ _ _ _ _ _ RS8 (proj2 (ref_at_setbn bs6 OW6 PL sdiv sd3 _ _) HAtmp6)) as HAtmp8.
    pose proof (ref_at_stable _ _ _ _ _ _ _ RS8 HAsnum7) as HAsnum8.
    pose proof (ref_at_stable _ _ _ _ _ _ _ RS8 (proj2 (ref_at_setbn bs6 OW6 PL sdiv sd3 _ _) HAsdiv6)) as HAsdiv8.
    assert (DN512 : Z.of_nat dn <= 512) by (clear - DNM OKs3; unfold bn_dmax in *; lia).
    assert (TN512 : Z.of_nat tn <= 512) by (clear - OKn2 OKn3; unfold tn, bn_dmax, BG_DMAX in *; lia).
    assert (LIMnb : limbs nbuf) by (unfold nbuf; apply splice_limbs; [exact OKs1 | exact LRES]).
    assert (Lnb2 : (dn <= length nbuf)%nat) by (rewrite Lnbuf; clear - DNM; lia).
    assert (HDN1 : (1 <= dn)%nat) by exact HTOPD5.
    assert (LIMnum : limbs (firstn tn (bn_buf bnum))) by (apply limbs_firstn; exact OKn1).
    assert (LENnum : length (firstn tn (bn_buf bnum)) = tn) by (apply firstn_length_le; exact OKn2).
    assert (Etopb6 : bn_top b6 = dn) by exact C6b.
    clear RS8 HAdv6 HArm6 HAnum6 HAdvs6 HAtmp6 HAsnum6 HAsdiv6 HAsnum7 HAnum7 ENV6 LS6 ENV7 LS7 LSH6 HWL6 WOK6 MU6' WM6' U9 BNsd WFS7 HVsn7 HVnum7 OKsn2
          PARTS6 WFS6 PWF6 IDS6 PLB6 ERRB6 ND6 Hinsd Hinpsd SEPsd DsdI DsdC Dsd0 SDA0 SDAC SDAI Rsd1 Rsd2 ARRsd LENnb ERRD SDLIN DSLIN ERLIN
          OKdv1 OKdv2 OKdv3 OKn1 OKn2 OKn3 C6b C6c C6d C6e HTOPD5 HTOPNZ5 Edtop Rdtop Ntop Eaft VRES Edsd OKs1 OKs2 OKs3 OKs4 HVsd6 LRES errv6 errv7.

    pose proof (RH_nodup_l _ _ _ _ (proj1 ENV8)) as ND8.
    destruct (lib_state_open [] bs8 m11 OW8 PL EA sdiv asdiv LS8 ND8 HAsdiv8 ltac:(intros []) NROsd) as ((Dsd8 & BNsd8 & _) & _ & _).
    destruct (lib_state_open [] bs8 m11 OW8 PL EA snum asnum LS8 ND8 HAsnum8 ltac:(intros []) NROs) as ((Dsn8 & BNsn8 & _) & (OKsn1 & OKsn2 & OKsn3 & OKsn4) & _).
    rewrite Esd8 in BNsd8. unfold bn_cells in BNsd8, BNsn8. unfold sd3 in BNsd8. cbn [bn_with_neg bn_with_buf bn_top bn_dmax bn_buf bn_neg bn_flags] in BNsd8.
    rewrite Etopb6 in BNsd8. rewrite L8b in BNsn8. fold tn in BNsn8. unfold BG_DMAX in OKsn3.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS8) as PARTS8.
    pose proof (ref_at_ualign _ _ _ _ _ _ _ _ _ (proj1 ENV8) PARTS8 HAsnum8 NROs) as (SNP & SN8).
    pose proof (ref_at_hrange _ _ _ _ _ _ _ _ _ (proj1 ENV8) PARTS8 HAsdiv8 HPd) as (SDA0 & SDAC & _ & _).
    pose proof (ref_at_hrange _ _ _ _ _ _ _ _ _ (proj1 ENV8) PARTS8 HAsnum8 HPs) as (SNA0 & SNAC & _ & _).
    assert (SNR : asnum + 24 <= alloc_ceiling) by (clear - SNAC; lia).
    assert (SDR : 0 < asdiv /\ asdiv + 24 <= alloc_ceiling) by (clear - SDA0 SDAC; lia).
    clear PARTS8 OKsn4.
    env_open ENV8.
    unfold MallocRep.wz in *. unfold implM. iprefix.
    zstep. if_cases KZ; zify_cond KZ. { exfalso. rewrite ?unsigned_lit in KZ by lia. lia. }
    clear KZ.
    step. step.
    chk ltac:(fun C => rewrite ?unsigned_lit in C by (clear - SNP SNR CEIL LO SPR; lia); clear - C SNP; lia).
    step. zstep. rewrite (land7 asnum) by exact SN8.
    chk ltac:(fun C => clear - C; lia).
    step. step. rewrite (zx32_small (Z.of_nat dn)) by (clear - DN512; lia).
    step.
    step. rewrite (sx32_small (Z.of_nat (tn + 1))) by (clear - TN512; lia).
    step. do 2 zstep.
    rewrite (bk_swrap32_small (Z.of_nat dn + 0)) by (unfold bn_dmax in *; lia). rewrite Z.add_0_r.
    step.
    env_close CSIL HWLs WOKs ENV8 LS8 ENV8' LS8'.

    ihere. to_implM. rewrite !bbind_get. rewrite Esd8. change (bn_top sd3) with (bn_top b6). rewrite Etopb6, L8b. fold tn.
    lazymatch type of ENV8' with cenv _ _ _ _ _ _ _ _ _ _ ?FR8 _ _ _ _ =>
    lazymatch goal with |- implM _ (interp (embed (bbind _ _ ?REST0 _))) _ ?Q _ =>
      enough (CONT : forall stP lsP mP OWP (nP : nat) x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x23 x24 x25 x28 x29 x30 x31,
                 cenv LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -256) s bs OW m FR8 stP lsP mP OWP -> lib_state lsP mP OWP PL EA ->
                 ref_at lsP OWP PL res ares -> oref_at lsP OWP PL rm arm -> ref_at lsP OWP PL num anum -> ref_at lsP OWP PL dvs advs ->
                 ref_at lsP OWP PL tmp atmp -> ref_at lsP OWP PL snum asnum -> ref_at lsP OWP PL sdiv asdiv ->
                 getbn sdiv lsP = sd3 ->
                 bn_top (getbn snum lsP) = nP -> (dn + 1 <= nP)%nat -> (tn + 1 <= nP)%nat -> Z.of_nat nP <= 513 ->
                 firstn nP (bn_buf (getbn snum lsP)) = lsh_res bnum sh ++ repeat 0%Z (nP - (tn + 1)) ->
                 implM bgusegs (interp (embed (REST0 tt lsP))) stP Q
                   (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -256)) gp (Z_to_bv 64 RATP) x5 x6 x7 sp x9 (Z_to_bv 64 (Z.of_nat dn)) x11 x12 x13 x14 x15 x16 x17
                            x18 (Z_to_bv 64 ares) (Z_to_bv 64 atmp) (Z_to_bv 64 asdiv) (Z_to_bv 64 anum) x23 x24 x25 (Z_to_bv 64 (Z.of_nat nP)) (Z_to_bv 64 advs) x28 x29 x30 x31)
                       F (Z_to_bv 64 0x109a0c) fc None mP (seg_rom bgusegs)))
    end end.
    { unfold implM. iprefix.
      zstep. rewrite lts_signed by (clear - DN512 TN512; lia). if_cases KB; zify_cond KB.
      -
        ihere. to_implM.
        replace (tn + 1 <=? dn)%nat with false by (symmetry; apply Nat.leb_gt; clear - KB; lia).
        rewrite bbind_ret.
        eapply (CONT st8 bs8 _ OW8 (tn + 1)%nat); [exact ENV8' | exact LS8' | try eassumption; try (clear - KB TN512; lia) ..].
        rewrite Nat.sub_diag. cbn [repeat]. rewrite app_nil_r. exact L8d.
      -
        ihere. to_implM.
        replace (tn + 1 <=? dn)%nat with true by (symmetry; apply Nat.leb_le; clear - KB; lia).
        lazymatch type of ENV8' with cenv _ _ _ _ _ _ _ _ _ _ ?FR8 _ _ _ _ =>
          split_cell FR8 (C8 (Z_to_bv 64 asnum)) ltac:(fun f1 rest =>
            split_cell rest (C8 (Z_to_bv 64 (Z.of_nat dn))) ltac:(fun f2 f3 =>
              lazymatch goal with |- implM _ (interp (embed (bbind _ _ ?REST0 _))) _ ?Q _ =>
                eapply (div_pad HM HF REST0 Q) with (snum := snum) (asnum := asnum) (dn := dn) (tnp := (tn + 1)%nat) (lo := lo) (B := B) (LB := LB) (PL := PL) (EA := EA)
                                                    (fr1 := f1) (fr2 := f2) (fr3 := f3)
              end))
        end.
        { exact CEIL. }
        { exact GLO'. }
        { clear - LO; lia. }
        { exact SPB. }
        { exact FROK. }
        { reflexivity. }
        { reflexivity. }
        { exact ENV8'. }
        { exact LS8'. }
        { exact HAsnum8. }
        { exact HPs. }
        { exact L8b. }
        { clear - KB; lia. }
        { clear - DN512; lia. }
        intros stP lsP mP OWP q1 q5 q6 q7 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 ENVP LSP RSP OTH TOPP NEGP FNP CTXP.
        eapply (CONT stP lsP mP OWP (dn + 1)%nat); [exact ENVP | exact LSP | exact (ref_at_stable _ _ _ _ _ _ _ RSP HAdv8) | exact (oref_at_stable _ _ _ _ _ _ _ RSP HArm8)
          | exact (ref_at_stable _ _ _ _ _ _ _ RSP HAnum8) | exact (ref_at_stable _ _ _ _ _ _ _ RSP HAdvs8) | exact (ref_at_stable _ _ _ _ _ _ _ RSP HAtmp8)
          | exact (ref_at_stable _ _ _ _ _ _ _ RSP HAsnum8) | exact (ref_at_stable _ _ _ _ _ _ _ RSP HAsdiv8) | | exact TOPP | clear; lia | clear - KB; lia | clear - DN512; lia | ].
        + rewrite OTH by (intros E; apply (hide_elim _ NEsd); symmetry; exact E). exact Esd8.
        + rewrite FNP, L8d. reflexivity. }

    intros stP lsP mP OWP nP q1 q5 q6 q7 q9 q11 q12 q13 q14 q15 q16 q17 q18 q23 q24 q25 q28 q29 q30 q31
           ENVP LSP HAdvP HArmP HAnumP HAdvsP HAtmpP HAsnumP HAsdivP GSP TNP NP1 NP2 N513 FNP.
    clear ENV8 LS8 ENV8' LS8' HAdv8 HArm8 HAnum8 HAdvs8 HAtmp8 HAsnum8 HAsdiv8 ND8 BNsd8 BNsn8 Dsd8 Dsn8 OKsn1 OKsn2 OKsn3 L8a L8b L8c L8d L8e Esd8 SDA0 SDAC SNA0 SNAC
          SNP SN8 SNR SDR.
    cbv beta. rewrite bbind_get, TNP.

    pose proof (RH_nodup_l _ _ _ _ (proj1 ENVP)) as NDP.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LSP) as PARTSP; pose proof PARTSP as (WFSP & PWFP & IDSP & PLBP & ERRBP).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LSP HAsdivP) as HVsdP. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LSP HAsnumP) as HVsnP.
    destruct (lib_state_open [] lsP mP OWP PL EA sdiv asdiv LSP NDP HAsdivP ltac:(intros []) NROsd) as ((DsdP & BNsdP & ARRsdP) & _ & _).
    destruct (lib_state_open [] lsP mP OWP PL EA snum asnum LSP NDP HAsnumP ltac:(intros []) NROs) as ((DsnP & BNsnP & ARRsnP) & (OKp1 & OKp2 & OKp3 & OKp4) & _).
    destruct (bn_arr_facts_w lsP OWP PL EA (bv_unsigned sp) B stP LB mP sdiv DsdP (proj1 ENVP) PARTSP FROK HVsdP (hpl_wref PL sdiv HPd) ARRsdP) as (UsdP & _ & DsdP0 & DsdPC & _ & _).
    rewrite GSP in BNsdP, UsdP, DsdPC. unfold bn_cells in BNsdP, BNsnP.
    unfold sd3 in BNsdP, UsdP, DsdPC. cbn [bn_with_neg bn_with_buf bn_top bn_dmax bn_buf bn_neg bn_flags] in BNsdP, UsdP, DsdPC.
    rewrite Etopb6 in BNsdP. rewrite TNP in BNsnP. unfold BG_DMAX in OKp3.
    unfold bn_dmax in DsdPC. cbn [bn_buf] in DsdPC. rewrite Lnbuf in DsdPC.
    assert (LENnbP : Z.of_nat (length (wlimbs nbuf)) = Z.of_nat (bn_dmax b6)) by (rewrite wlimbs_len, Lnbuf; reflexivity).
    set (d0 := nth (dn - 1) nbuf 0).
    set (d1 := if (dn =? 1)%nat then 0 else nth (dn - 2) nbuf 0).
    assert (Rd0 : 9223372036854775808 <= d0 < 18446744073709551616).
    { assert (L : limb d0) by (apply limbs_nth; exact LIMnb). unfold limb in L. rewrite BW_lit in L. split; [|clear - L; lia].
      unfold d0, nbuf, splice. change (firstn 0 (bn_buf b6)) with (@nil Z). cbn [app]. rewrite app_nth1 by (clear - Lres HDN1; lia).
      change (2 ^ 63) with 9223372036854775808 in D0N. exact D0N. }
    assert (Rd1 : 0 <= d1 < 18446744073709551616).
    { unfold d1. destruct (dn =? 1)%nat; [clear; lia|]. assert (L : limb (nth (dn - 2) nbuf 0)) by (apply limbs_nth; exact LIMnb). unfold limb in L. rewrite BW_lit in L. clear - L. lia. }
    pose proof (ref_at_hrange _ _ _ _ _ _ _ _ _ (proj1 ENVP) PARTSP HAsdivP HPd) as (SP0 & SPC & _ & _).
    pose proof (ref_at_hrange _ _ _ _ _ _ _ _ _ (proj1 ENVP) PARTSP HAsnumP HPs) as (NP0 & NPC & _ & _).
    assert (DNDM : Z.of_nat dn <= Z.of_nat (bn_dmax b6)) by exact DNM.
    assert (NPDM : Z.of_nat nP <= Z.of_nat (bn_dmax (getbn snum lsP))) by (clear - OKp2 TNP; lia).
    apply hide_intro in OKp4.
    assert (HSN : exists psn, bn_d (getbn snum lsP) = Some psn /\ In (psn, DsnP, 8 * Z.of_nat (bn_dmax (getbn snum lsP))) OWP).
    { destruct (bn_d (getbn snum lsP)) as [psn|] eqn:Edsn0; [exists psn; split; [reflexivity|]; unfold bn_arr in ARRsnP; rewrite Edsn0 in ARRsnP; exact (proj1 ARRsnP)|].
      exfalso. destruct (bn_arr_null PL snum mP OWP DsnP _ PWFP (hpl_wref PL snum HPs) Edsn0 ARRsnP) as [_ E]. unfold bn_dmax in NPDM. rewrite E in NPDM. cbn in NPDM. clear - NPDM NP1. lia. }
    destruct HSN as (psn & Edsn & HinsnP).
    pose proof (block_ualign _ _ _ _ _ _ _ (proj1 ENVP) HinsnP) as (SNDP & SND8).
    pose proof (bn_arr_ualign _ _ _ _ _ _ _ _ _ _ (proj1 ENVP) PARTSP ARRsdP ltac:(rewrite GSP; unfold sd3, bn_dmax; cbn [bn_with_neg bn_with_buf bn_buf]; clear - Lnb2 HDN1; lia)) as (SDDP & SDD8).
    destruct (bn_arr_facts_w lsP OWP PL EA (bv_unsigned sp) B stP LB mP snum DsnP (proj1 ENVP) PARTSP FROK HVsnP (hpl_wref PL snum HPs) ARRsnP) as (_ & _ & _ & DsnPC & _ & _).
    set (loop := (nP - dn)%nat) in *.
    assert (RLOOP : 0 < Z.of_nat loop < 8388609) by (unfold loop, bn_dmax in *; lia).
    assert (RNP : 0 < Z.of_nat nP < 8388609) by (unfold bn_dmax in *; lia).
    assert (RDN : 0 < Z.of_nat dn < 8388609) by (unfold bn_dmax in *; lia).
    assert (RSNP : DsnP + 8 * Z.of_nat nP <= alloc_ceiling) by (unfold bn_dmax in *; lia).
    assert (RSDP : DsdP + 8 * Z.of_nat dn <= alloc_ceiling) by (unfold bn_dmax in *; lia).
    env_open ENVP.
    unfold MallocRep.wz in *. unfold implM. iprefix.
    repeat match goal with H : _ \/ _ |- _ => apply hide_intro in H end.
    do 2 zstep.
    rewrite (bk_swrap32_small (Z.of_nat nP - Z.of_nat dn)) by (clear - RNP RDN; lia).
    replace (Z.of_nat nP + - Z.of_nat dn) with (Z.of_nat loop) by (unfold loop; clear - NP1; lia).
    replace (Z.of_nat nP - Z.of_nat dn) with (Z.of_nat loop) by (unfold loop; clear - NP1; lia).
    step.
    chk ltac:(fun C => clear - C; lia).
    step. step. step. do 2 zstep.
    replace (Z.of_nat loop ≪ 3) with (8 * Z.of_nat loop) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    do 2 zstep. rewrite ?land64_small by (clear - SNDP RSNP RLOOP NP1 CEIL LO SPR; unfold loop in *; lia).
    replace (0 <? DsnP) with true by (symmetry; apply Z.ltb_lt; exact SNDP).
    replace (DsnP + 8 * Z.of_nat loop <? 1) with false by (symmetry; apply Z.ltb_ge; clear - SNDP; lia).
    cbn [Z.b2z].
    chk ltac:(fun C => clear - C; lia).
    zstep. step. do 3 zstep.
    rewrite (lxor_signbit63' (Z.of_nat loop)) by (clear - RLOOP; lia).
    replace (Z.of_nat loop + 9223372036854775808 <? 9223372036854775808) with false by (symmetry; apply Z.ltb_ge; clear; lia).
    replace (DsnP + 8 * Z.of_nat loop <? 8 * Z.of_nat loop) with false by (symmetry; apply Z.ltb_ge; clear - SNDP; lia).
    cbn [Z.b2z Z.lxor].
    chk ltac:(fun C => clear - C; lia).
    zstep. rewrite (bk_swrap32_small (Z.of_nat nP + -1)) by (clear - RNP; lia).
    zstep. rewrite lts_signed by (clear - RNP; lia). if_cases KO; zify_cond KO. { exfalso. clear - KO. lia. } clear KO.
    do 2 zstep.
    replace (DsnP + (Z.of_nat nP + -1) ≪ 3) with (DsnP + 8 * (Z.of_nat nP - 1)) by (rewrite Z.shiftl_mul_pow2 by lia; clear; lia).
    step.
    zstep. rewrite ?land64_small by (clear - SNDP RSNP RNP CEIL LO SPR; lia).
    replace (DsnP + 8 * (Z.of_nat nP - 1) <? 1) with false by (symmetry; apply Z.ltb_ge; clear - SNDP RNP; lia).
    cbn [Z.b2z].
    chk ltac:(fun C => clear - C; lia).
    step. do 4 zstep.
    rewrite (lxor_signbit63' (Z.of_nat nP + -1)) by (clear - RNP; lia).
    replace (Z.of_nat nP + -1 + 9223372036854775808 <? 9223372036854775808) with false by (symmetry; apply Z.ltb_ge; clear - RNP; lia).
    replace (DsnP + 8 * (Z.of_nat nP - 1) <? DsnP) with false by (symmetry; apply Z.ltb_ge; clear - RNP; lia).
    cbn [Z.b2z Z.lxor].
    chk ltac:(fun C => clear - C; lia).
    step.
    zstep. rewrite (bk_swrap32_small (Z.of_nat dn + -1)) by (clear - RDN; lia).
    zstep. rewrite lts_signed by (clear - RDN; lia). if_cases KO; zify_cond KO. { exfalso. clear - KO. lia. } clear KO.
    step. step. do 2 zstep.
    replace (DsdP + (Z.of_nat dn + -1) ≪ 3) with (DsdP + 8 * (Z.of_nat dn - 1)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    do 2 zstep. rewrite ?land64_small by (clear - SDDP RSDP RDN CEIL LO SPR; lia).
    replace (0 <? DsdP) with true by (symmetry; apply Z.ltb_lt; exact SDDP).
    replace (DsdP + 8 * (Z.of_nat dn - 1) <? 1) with false by (symmetry; apply Z.ltb_ge; clear - SDDP RDN; lia).
    cbn [Z.b2z].
    chk ltac:(fun C => clear - C; lia).
    do 4 zstep.
    rewrite (lxor_signbit63' (Z.of_nat dn + -1)) by (clear - RDN; lia).
    replace (Z.of_nat dn + -1 + 9223372036854775808 <? 9223372036854775808) with false by (symmetry; apply Z.ltb_ge; clear - RDN; lia).
    replace (DsdP + 8 * (Z.of_nat dn - 1) <? DsdP) with false by (symmetry; apply Z.ltb_ge; clear - RDN; lia).
    cbn [Z.b2z Z.lxor].
    chk ltac:(fun C => clear - C; lia).
    chk ltac:(fun C => rewrite ?unsigned_lit in C by (clear - SDDP RSDP CEIL LO SPR; lia); clear - C SDDP; lia).
    zstep. rewrite (land7 (DsdP + 8 * (Z.of_nat dn - 1))) by (clear - SDD8; Z.div_mod_to_equations; lia).
    chk ltac:(fun C => clear - C; lia).
    assert (N0 : nth_error nbuf (dn - 1) = Some d0) by (unfold d0; apply nth_error_nth'; lia).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mR end.
    destruct (proj1 (limbarr_limbs_at bgusegs mR DsdP nbuf) UsdP) as (LAnbR & _).
    let ad := cur_mem_addr in
      pose proof (limbs_at_read_nth bgusegs mR DsdP nbuf (dn - 1) d0 ad LAnbR N0 ltac:(unfold wa; f_equal; lia)) as RD.
    zstep. clear RD.
    zstep. step.
    eassert (C6D8 : _); [ |
      zstep; if_cases K1; zify_cond K1;
      [
        assert (N1 : nth_error nbuf (dn - 2) = Some d1)
          by (unfold d1; replace (dn =? 1)%nat with false by (symmetry; apply Nat.eqb_neq; lia); apply nth_error_nth'; lia);
        assert (DN2 : 2 <= Z.of_nat dn) by (rewrite ?unsigned_lit in K1 by (clear - RDN; lia); clear - K1 RDN; lia);
        zstep; rewrite (bk_swrap32_small (Z.of_nat dn + -2)) by (clear - RDN DN2; lia);
        zstep; rewrite lts_signed by (clear - RDN DN2; lia); if_cases KO; zify_cond KO; [exfalso; clear - KO; lia | clear KO];
        do 2 zstep;
        replace (DsdP + (Z.of_nat dn + -2) ≪ 3) with (DsdP + 8 * (Z.of_nat dn - 2)) by (rewrite Z.shiftl_mul_pow2 by lia; lia);
        chk ltac:(fun C => rewrite ?unsigned_lit in C by (clear - SDDP RSDP DN2 CEIL LO SPR; lia); clear - C SDDP DN2; lia);
        do 4 zstep;
        rewrite (lxor_signbit63' (Z.of_nat dn + -2)) by (clear - RDN DN2; lia);
        replace (Z.of_nat dn + -2 + 9223372036854775808 <? 9223372036854775808) with false by (symmetry; apply Z.ltb_ge; clear - DN2; lia);
        replace (DsdP + 8 * (Z.of_nat dn - 2) <? DsdP) with false by (symmetry; apply Z.ltb_ge; clear - DN2; lia);
        cbn [Z.b2z Z.lxor];
        chk ltac:(fun C => clear - C; lia);
        zstep; rewrite (land7 (DsdP + 8 * (Z.of_nat dn - 2))) by (clear - SDD8; Z.div_mod_to_equations; lia);
        chk ltac:(fun C => clear - C; lia);
        (let ad := cur_mem_addr in
         pose proof (limbs_at_read_nth bgusegs mR DsdP nbuf (dn - 2) d1 ad LAnbR N1 ltac:(unfold wa; f_equal; lia)) as RD);
        zstep; clear RD; forget_temps; exact C6D8
      | do 2 zstep;
        setreg_at 18%Z (Z_to_bv 64 d1) ltac:(unfold d1; replace (dn =? 1)%nat with true by (symmetry; apply Nat.eqb_eq; rewrite ?unsigned_lit in K1 by (clear - RDN; lia); clear - K1; lia); reflexivity);
        forget_temps; exact C6D8 ] ].
    intros j5 j6 j7 j10 j11 j12 j13 j14 j15 j16 j17 j28 j29 j30 j31.
    zstep. step. zstep.
    repeat match goal with H : hide (_ \/ _) |- _ => apply hide_elim in H end.
    env_close CSIL HWLs WOKs ENVP LSP ENVQ LSQ.
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LSP HAdvP) as HVdvP.
    pose proof (st_wf_ok res lsP WFSP HVdvP NROr) as (_ & OKdvP2 & _).
    destruct (CPRE _ _ _ _ _ BN_WEXPAND_STACK ENVQ LSQ ltac:(unfold BN_WEXPAND_STACK, BN_EXPAND2_STACK; lia)) as (errvQ & PREQ).
    ihere. to_implM. unfold bbind at 1. cbn [bind tree_ops].
    eapply implM_embed_bind.
    { eapply BnLeaves.implM_embed_leaves; [apply (bn_wexpand_leaves2 res loop lsP HVdvP OKdvP2)|].
      eapply (bn_wexpand_walk HM HF) with (lo := lo) (B := B) (errv := errvQ) (r := res) (a := ares) (OW := OWP) (LB := LB) (PL := PL) (EA := EA) (words := loop);
        [exact PREQ | reflexivity | exact HAdvP | exact WRres | reflexivity | reflexivity | clear - N513; unfold loop; lia]. }
    cbv beta. intros [uR lsR] stR msR [PO LEAFR]. apply BPC in PO.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & mS & OWR & PLR & -> & CPR & (EPLR & -> & HDMR & _ & BLKR)).
    subst PLR. specialize (CPR eq_refl).
    destruct (CPOST _ _ _ _ _ _ _ _ _ ENVQ CPR) as (ENVR & LSR).
    pose proof (cpost_refs LB PL EA lo B (bv_unsigned sp + -256) _ _ _ _ _ _ _ _ CPR) as RSR.
    cbn [fst snd] in *.
    replace (ret_pc (Z_to_bv 64 1088296)) with (Z_to_bv 64 1088296) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    clear PREQ CPR.

    destruct LEAFR as (R1 & R2 & R3 & R4 & R5 & RD & _ & _). cbn [snd] in *.
    pose proof (ref_at_stable _ _ _ _ _ _ _ RSR HAdvP) as HAdvR. pose proof (oref_at_stable _ _ _ _ _ _ _ RSR HArmP) as HArmR.
    pose proof (ref_at_stable _ _ _ _ _ _ _ RSR HAnumP) as HAnumR. pose proof (ref_at_stable _ _ _ _ _ _ _ RSR HAdvsP) as HAdvsR.
    pose proof (ref_at_stable _ _ _ _ _ _ _ RSR HAtmpP) as HAtmpR. pose proof (ref_at_stable _ _ _ _ _ _ _ RSR HAsnumP) as HAsnumR.
    pose proof (ref_at_stable _ _ _ _ _ _ _ RSR HAsdivP) as HAsdivR.
    assert (GSR : getbn sdiv lsR = sd3) by (rewrite R1 by exact NEvd; exact GSP).
    assert (GNR : getbn snum lsR = getbn snum lsP) by (apply R1; exact NEvs).

    assert (HinsnR : In (psn, DsnP, 8 * Z.of_nat (bn_dmax (getbn snum lsP))) OWR).
    { apply BLKR; [exact HinsnP|]. intros E.
      eapply (ids_bn_neq res snum lsP psn psn (ids_m_nodup _ _ _ IDSP) HVdvP HVsnP (hide_elim _ NEvs) E Edsn). reflexivity. }
    clear BLKR RSR HAdvP HArmP HAnumP HAdvsP HAtmpP HAsnumP HAsdivP ENVP LSP ENVQ LSQ NDP PARTSP WFSP PWFP IDSP PLBP ERRBP HVsdP HVsnP HVdvP OKdvP2
          BNsdP BNsnP ARRsdP ARRsnP UsdP HinsnP SP0 SPC NP0 NPC DsdP0 DsdPC LAnbR N0.
    pose proof (RH_nodup_l _ _ _ _ (proj1 ENVR)) as NDR.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LSR) as PARTSR; pose proof PARTSR as (WFSR & PWFR & IDSR & PLBR & ERRBR).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LSR HAdvR) as HVdvR.
    destruct (lib_state_open [] lsR mS OWR PL EA num anum LSR NDR HAnumR ltac:(intros []) NROn) as ((DnumR & BNnumR & _) & _ & _).
    destruct (lib_state_open [] lsR mS OWR PL EA dvs advs LSR NDR HAdvsR ltac:(intros []) NROd) as ((DdvsR & BNdvsR & _) & _ & _).
    destruct (lib_state_open [] lsR mS OWR PL EA res ares LSR NDR HAdvR ltac:(intros []) NROr) as ((Ddv & BNdv & ARRdv) & (OKv1 & OKv2 & OKv3 & OKv4) & LSHR).
    unfold bn_cells in BNnumR, BNdvsR, BNdv.
    set (bv := getbn res lsR) in *. set (bnR := getbn num lsR) in *. set (bdR := getbn dvs lsR) in *.
    pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ (proj1 ENVR) PARTSR FROK HAdvR NROr) as (V0 & VC & VI).
    pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ (proj1 ENVR) PARTSR FROK HAnumR NROn) as (N0' & NC' & _).
    pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ (proj1 ENVR) PARTSR FROK HAdvsR NROd) as (D0' & DC' & _).
    assert (ARES : 0 < ares /\ ares + 24 < 18446744073709551616) by (clear - V0 VC CEIL LO SPR; lia).
    assert (ANUM : 0 < anum /\ anum + 24 < 18446744073709551616) by (clear - N0' NC' CEIL LO SPR; lia).
    assert (ADVS : 0 < advs /\ advs + 24 < 18446744073709551616) by (clear - D0' DC' CEIL LO SPR; lia).
    assert (VCF : ares + 24 <= bv_unsigned sp - 256 \/ bv_unsigned sp <= ares) by (clear - VC CEIL LO; lia).
    assert (VIE : ares + 24 <= 3346164 \/ 3346164 + 4 <= ares) by (clear - VI; lia).
    clear N0' NC' D0' DC' V0 VC VI.
    repeat match goal with H : _ \/ _ |- _ => apply hide_intro in H end.
    apply hide_elim in VCF. apply hide_elim in VIE.
    destruct (bn_arr_facts_w lsR OWR PL EA (bv_unsigned sp) B stR LB mS res Ddv (proj1 ENVR) PARTSR FROK HVdvR WRres ARRdv) as (_ & _ & DV0 & DVC & _ & _).
    pose proof (bn_arr_ualign _ _ _ _ _ _ _ _ _ _ (proj1 ENVR) PARTSR ARRdv ltac:(clear - RD RLOOP; lia)) as (DVP & DV8).
    pose proof (ref_at_ualign _ _ _ _ _ _ _ _ _ (proj1 ENVR) PARTSR HAnumR NROn) as (ANP & AN8).
    pose proof (ref_at_ualign _ _ _ _ _ _ _ _ _ (proj1 ENVR) PARTSR HAdvsR NROd) as (ADP & AD8).
    pose proof (ref_at_ualign _ _ _ _ _ _ _ _ _ (proj1 ENVR) PARTSR HAdvR NROr) as (AVP & AV8).
    fold bv in DVC. assert (RDV : Ddv + 8 * Z.of_nat loop <= alloc_ceiling) by (clear - DVC RD; unfold bn_dmax in *; lia).
    env_open ENVR.
    match goal with MUx : munch _ mS mS |- _ => clear MUx end.
    pose proof (munch_refl [(bv_unsigned sp + -256, bv_unsigned sp); (ares, ares + 24)]%Z mS) as MUR.
    unfold MallocRep.wz in *. unfold implM. iprefix.
    zstep. if_cases KZ; zify_cond KZ. { exfalso. rewrite ?unsigned_lit in KZ by (clear - ARES; lia). clear - KZ ARES. lia. }
    clear KZ.
    chk ltac:(fun C => rewrite ?unsigned_lit in C by lia; lia).
    zstep. rewrite (land7 anum) by exact AN8.
    chk ltac:(fun C => clear - C; lia).
    chk ltac:(fun C => rewrite ?unsigned_lit in C by lia; lia).
    zstep. rewrite (land7 advs) by exact AD8.
    chk ltac:(fun C => clear - C; lia).
    chk ltac:(fun C => rewrite ?unsigned_lit in C by lia; lia).
    zstep. rewrite (land7 ares) by exact AV8.
    chk ltac:(fun C => clear - C; lia).
    step. rewrite (sx32_small (Z.b2z (bn_neg bnR))) by (destruct (bn_neg bnR); cbn; lia).
    step.
    step. rewrite (sx32_small (Z.b2z (bn_neg bdR))) by (destruct (bn_neg bdR); cbn; lia).
    zstep. step. zstep.
    setreg_at 10%Z (Z_to_bv 64 (Z.b2z (xorb (bn_neg bnR) (bn_neg bdR)))) ltac:(f_equal; destruct (bn_neg bnR), (bn_neg bdR); reflexivity).
    try clear BNnumR. try clear BNdvsR. clear DnumR DdvsR.
    do 2 zstep. rewrite ?land64_small by (clear - DVP RDV RLOOP CEIL LO SPR; lia).
    replace (0 <? Ddv) with true by (symmetry; apply Z.ltb_lt; exact DVP).
    replace (8 * Z.of_nat loop + Ddv <? 1) with false by (symmetry; apply Z.ltb_ge; clear - DVP; lia).
    cbn [Z.b2z].
    step. step. step.
    chk ltac:(fun C => clear - C; lia).
    do 3 zstep.
    replace (8 * Z.of_nat loop + Ddv <? 8 * Z.of_nat loop) with false by (symmetry; apply Z.ltb_ge; clear - DVP; lia).
    cbn [Z.b2z Z.lxor].
    chk ltac:(fun C => clear - C; lia).
    step. zstep.
    rewrite (bk_swrap32_small (Z.of_nat dn + 1)) by (clear - DN512; lia).
    zstep. step. zstep.

    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mT end.
    ihere. to_implM. rewrite !bbind_get. fold bnR bdR. rewrite bbind_get_set. fold bv.
    set (q2 := mkBN (bn_d bv) (bn_buf bv) loop (xorb (bn_neg bnR) (bn_neg bdR)) (bn_flags bv)).
    assert (WOKR : Forall (w_ok OWR LB lsR PL EA (bv_unsigned sp) [res]) [(bv_unsigned sp + -256, bv_unsigned sp); (ares, ares + 24)]).
    { constructor; [apply w_stack; cbn [fst snd]; clear - CEIL LO; lia|]. constructor; [eapply (w_struct OWR LB lsR PL EA (bv_unsigned sp) false [res] _ res ares); [left; reflexivity| exact HAdvR| exact NROr| cbn; lia| cbn; lia]| constructor]. }
    assert (HWLR : Forall (w_lib lsR OWR PL lo (bv_unsigned sp)) [(bv_unsigned sp + -256, bv_unsigned sp); (ares, ares + 24)]).
    { constructor; [left; cbn [fst snd]; clear - LO; lia|]. constructor; [right; right; exists res, ares; split; [exact HAdvR| split; [exact NROr| cbn [fst snd]; clear; lia]]| constructor]. }
    assert (LST : lib_state (setbn res q2 lsR) mT OWR PL EA).
    { unfold lib_state. eapply (lib_state_close [] lsR mT OWR PL EA res ares); [| exact NDR| exact HAdvR| exact NROr| | |].
      - match goal with HEAPx : RHEAP stR _ mS, WMx : wmono _ mS mT |- _ => exact (lib_state_frame stR LB _ _ [res] lsR mS mT OWR PL EA _ HEAPx LSHR MUR WMx FROK WOKR) end.
      - exists Ddv. split.
        + unfold bn_cells, q2, bn_dmax. cbn [bn_top bn_buf bn_neg bn_flags]. exact BNdv.
        + destruct (bn_d bv) as [pv|] eqn:Edv.
          * unfold bn_arr, q2 in *. cbn [bn_d bn_buf bn_dmax] in *. rewrite Edv in *. destruct ARRdv as [Hin Uarr]. split; [exact Hin|].

            match goal with WMx : wmono _ mS mT |- _ => eapply u64arr_transport; [exact Uarr | exact MUR | exact WMx |] end.
            pose proof (RH_range _ _ _ _ _ _ _ (proj1 ENVR) Hin) as (_ & _ & _ & PC & _).
            pose proof (struct_limbs_disj stR OWR LB mS (proj1 ENVR) lsR PL EA (bv_unsigned sp) B PARTSR FROK res res ares pv Ddv _ HAdvR HVdvR Edv Hin) as SLD.
            cbn [disjoint_from]. rewrite wlimbs_len. fold (bn_dmax bv). clear - PC SLD CEIL LO. lia.
          * destruct (bn_arr_null PL res mS OWR Ddv bv PWFR WRres Edv ARRdv) as [E0 Eb].
            apply (bn_arr_nil_intro PL res mT OWR Ddv q2 PWFR WRres E0); [exact Eb| first [exact Edv | reflexivity]].
      - unfold bg_ok, q2, bn_dmax in *. cbn [bn_buf bn_top bn_flags]. split; [exact OKv1|]. split; [exact RD|]. split; [exact OKv3| exact OKv4].
      - apply ids_ok_setbn_same; [exact IDSR| exact HVdvR| reflexivity]. }
    lazymatch type of ENVR with cenv ?a ?b ?c ?d ?e ?f ?g ?h ?i ?j _ _ _ _ _ =>
      lazymatch goal with FRx : rw_cells _ mT (bv_unsigned sp + -256) ?fr' |- _ =>
        assert (ENVT : cenv a b c d e f g h i j fr' stR (setbn res q2 lsR) mT OWR) end end.
    { apply cenv_setbn.
      match goal with FRx : rw_cells _ mT (bv_unsigned sp + -256) ?fr', STx : stk _ mT _ _, MIx : mem_inv _ mT, ERRx : rw_cells _ mT 3346164 _, WMx : wmono _ mS mT |- _ =>
        eapply (CSIL _ fr'); [exact ENVR | exact LSR | exact MUR | exact WMx | exact HWLR | exact STx | unfold LX_ERRNO, RATP; exact ERRx | exact MIx | exact FRx | cbn; lia] end. }
    set (lsT := setbn res q2 lsR) in *.
    assert (HAtmpT : ref_at lsT OWR PL tmp atmp) by (apply ref_at_setbn; exact HAtmpR).
    pose proof (lib_state_h_parts _ _ _ _ _ _ LST) as (WFST & PWFT & IDST & _).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LST HAtmpT) as HVtT.
    pose proof (st_wf_ok tmp lsT WFST HVtT NROt) as (_ & OKtT2 & _).

    assert (LOOP1 : (1 <= loop)%nat) by (unfold loop; clear - NP1; lia).
    assert (HDV : exists pv, bn_d bv = Some pv /\ In (pv, Ddv, 8 * Z.of_nat (bn_dmax bv)) OWR).
    { destruct (bn_d bv) as [pv|] eqn:Edv0; [exists pv; split; [reflexivity|]; unfold bn_arr in ARRdv; rewrite Edv0 in ARRdv; exact (proj1 ARRdv)|].
      exfalso. destruct (bn_arr_null PL res mS OWR Ddv bv PWFR WRres Edv0 ARRdv) as [_ E]. unfold bn_dmax in RD. rewrite E in RD. cbn in RD. clear - RD LOOP1. lia. }
    destruct HDV as (pv & Edv & Hinpv).
    destruct (CPRE _ _ _ _ _ BN_WEXPAND_STACK ENVT LST ltac:(unfold BN_WEXPAND_STACK, BN_EXPAND2_STACK; clear - LO; lia)) as (errvT & PRET).
    unfold bbind at 1. cbn [bind tree_ops].
    eapply implM_embed_bind.
    { eapply BnLeaves.implM_embed_leaves; [apply (bn_wexpand_leaves2 tmp (dn + 1) lsT HVtT OKtT2)|].
      eapply (bn_wexpand_walk HM HF) with (lo := lo) (B := B) (errv := errvT) (r := tmp) (a := atmp) (OW := OWR) (LB := LB) (PL := PL) (EA := EA) (words := (dn + 1)%nat);
        [exact PRET | reflexivity | exact HAtmpT | exact (hpl_wref PL tmp HPt) | reflexivity | f_equal; f_equal; clear; lia | clear - DN512; lia]. }
    cbv beta. intros [uU lsU] stU msU [PO LEAFU]. apply BPC in PO.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & mU & OWU & PLU & -> & CPU & (EPLU & -> & HDMU & _ & BLKU)).
    subst PLU. specialize (CPU eq_refl).
    destruct (CPOST _ _ _ _ _ _ _ _ _ ENVT CPU) as (ENVU & LSU).
    pose proof (cpost_refs LB PL EA lo B (bv_unsigned sp + -256) _ _ _ _ _ _ _ _ CPU) as RSU.
    cbn [fst snd] in *.
    replace (ret_pc (Z_to_bv 64 1088420)) with (Z_to_bv 64 1088420) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    clear PRET CPU.

    destruct LEAFU as (U1 & U2 & U3 & U4 & U5 & UD & _ & _). cbn [snd] in *.
    pose proof (ref_at_stable _ _ _ _ _ _ _ RSU (proj2 (ref_at_setbn lsR OWR PL res q2 _ _) HAdvR)) as HAdvU.
    pose proof (oref_at_stable _ _ _ _ _ _ _ RSU (oref_at_setbn lsR OWR PL res q2 _ _ HArmR)) as HArmU.
    pose proof (ref_at_stable _ _ _ _ _ _ _ RSU HAtmpT) as HAtmpU.
    pose proof (ref_at_stable _ _ _ _ _ _ _ RSU (proj2 (ref_at_setbn lsR OWR PL res q2 _ _) HAsnumR)) as HAsnumU.
    pose proof (ref_at_stable _ _ _ _ _ _ _ RSU (proj2 (ref_at_setbn lsR OWR PL res q2 _ _) HAsdivR)) as HAsdivU.
    assert (GSU : getbn sdiv lsU = sd3) by (rewrite U1 by exact NEtd; unfold lsT; rewrite getbn_setbn_other by exact NEvd; exact GSR).
    assert (GNU : getbn snum lsU = getbn snum lsP) by (rewrite U1 by exact NEts; unfold lsT; rewrite getbn_setbn_other by exact NEvs; exact GNR).
    assert (GVU : getbn res lsU = q2) by (rewrite U1 by (apply not_eq_sym; exact NEvt); unfold lsT; apply getbn_setbn_same; exact HVdvR).
    assert (HinsnU : In (psn, DsnP, 8 * Z.of_nat (bn_dmax (getbn snum lsP))) OWU).
    { apply BLKU; [exact HinsnR|]. intros E.
      assert (HVsT : vref snum lsT) by (apply vref_setbn; apply (ref_at_valid _ _ _ _ _ _ _ _ LSR HAsnumR)).
      eapply (ids_bn_neq tmp snum lsT psn psn (ids_m_nodup _ _ _ IDST) HVtT HVsT (hide_elim _ NEts) E); [|reflexivity].
      unfold lsT. rewrite getbn_setbn_other by exact NEvs. rewrite GNR. exact Edsn. }
    assert (HinpvU : In (pv, Ddv, 8 * Z.of_nat (bn_dmax bv)) OWU).
    { apply BLKU; [exact Hinpv|]. intros E.
      assert (HVvT : vref res lsT) by (apply vref_setbn; exact HVdvR).
      eapply (ids_bn_neq tmp res lsT pv pv (ids_m_nodup _ _ _ IDST) HVtT HVvT (not_eq_sym (hide_elim _ NEvt)) E); [|reflexivity].
      unfold lsT. rewrite getbn_setbn_same by exact HVdvR. exact Edv. }
    set (bsn := getbn snum lsP) in *.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LSU) as PARTSU.
    pose proof (ref_at_hrange _ _ _ _ _ _ _ _ _ (proj1 ENVU) PARTSU HAtmpU HPt) as (T0' & TC' & _ & _).
    assert (ATMP : 0 < atmp /\ atmp + 24 < 18446744073709551616) by (clear - T0' TC' CEIL LO SPR; lia).
    pose proof (ref_at_ualign _ _ _ _ _ _ _ _ _ (proj1 ENVU) PARTSU HAtmpU (proj1 HPt)) as (ATP & AT8).
    pose proof (block_ualign _ _ _ _ _ _ _ (proj1 ENVU) HinpvU) as (DVPu & DV8u).
    pose proof (block_ualign _ _ _ _ _ _ _ (proj1 ENVU) HinsnU) as (SNPu & SN8u).
    clear BLKU RSU HAdvR HArmR HAnumR HAdvsR HAtmpR HAsnumR HAsdivR HAtmpT ENVR LSR ENVT LST LSHR NDR PARTSR WFSR PWFR IDSR PLBR ERRBR WFST PWFT IDST HVtT OKtT2 HVdvR
          HinsnR Hinpv WOKR HWLR MUR BNdv ARRdv GSR GNR R1 R2 R3 R4 R5 PARTSU T0' TC' VCF VIE ARES ANUM ADVS.
    env_open ENVU.
    unfold MallocRep.wz in *. unfold implM. iprefix.
    zstep. if_cases KZ; zify_cond KZ. { exfalso. rewrite ?unsigned_lit in KZ by (clear - ATMP; lia). clear - KZ ATMP. lia. }
    clear KZ.
    do 4 zstep. step. do 2 zstep. step. zstep. step. do 2 zstep. step. step. do 2 zstep. step.
    zstep.
    remember (Z_to_bv 64 4294967295) as mask32 eqn:Emask.
    step. subst mask32.
    zstep. step. do 2 zstep. step. step.
    replace (Z.land d1 4294967295) with (d1 mod 4294967296) in FRe0 by (change 4294967295 with (Z.ones 32); rewrite Z.land_ones by lia; reflexivity).
    rewrite (land7 Ddv) in FRe0 |- * by exact DV8u.
    rewrite (land7 DsnP) in FRe0 by exact SN8u.
    rewrite (land7 atmp) in FRe0 by exact AT8.
    rewrite (lxor_signbit63' (Z.of_nat dn)) in FRe0 by (clear - RDN; lia).
    replace (Z.of_nat dn + 9223372036854775808 <? 9223372036854775808) with false in FRe0 by (symmetry; apply Z.ltb_ge; clear; lia).
    replace (0 <? atmp) with true in FRe0 by (symmetry; apply Z.ltb_lt; exact ATP).
    change (0 <? 1) with true in FRe0. change (Z.b2z false) with 0 in FRe0. change (Z.b2z true) with 1 in FRe0. change (Z.land 1 1) with 1 in FRe0.
    replace (Z.of_nat dn ≪ 3) with (8 * Z.of_nat dn) in FRe0 |- * by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    replace (DsnP + 8 * (Z.of_nat nP - 1)) with (DsnP + 8 * Z.of_nat (nP - 1)) in FRe0 by (clear - RNP; lia).
    replace (8 * Z.of_nat loop + Ddv) with (Ddv + 8 * Z.of_nat loop) by (clear; lia).
    env_close CSIL HWLs WOKs ENVU LSU ENVV LSV.
    ihere. to_implM.
    eapply (div_tail HM HF) with (res := res) (rm := rm) (tmp := tmp) (snum := snum) (sdiv := sdiv)
             (adv := ares) (arm := arm) (atmp := atmp) (asnum := asnum) (asdiv := asdiv) (ac := ac) (qc := qc) (psn := psn) (pv := pv) (sdbuf := nbuf) (negn := bn_neg bnR)
             (dn := dn) (loop := loop) (nP := nP) (d0 := d0) (d1 := d1) (sh := sh) (DsnP := DsnP) (Ddv := Ddv).
    { exact CEIL. }
    { exact GLO'. }
    { clear - LO; lia. }
    { exact SPB. }
    { exact FROK. }
    { exact EC. }
    { exact ENVV. }
    { exact LSV. }
    { exact HAdvU. }
    { exact HArmU. }
    { exact HAtmpU. }
    { exact HAsnumU. }
    { exact HAsdivU. }
    { exact WRres. }
    { exact HPrm. }
    { exact HPt. }
    { exact HPs. }
    { exact HPd. }
    { exact NEts. }
    { exact NEtd. }
    { exact NEsd. }
    { exact NEvt. }
    { exact NEvs. }
    { exact NEvd. }
    { rewrite GSU. reflexivity. }
    { rewrite GSU. exact Etopb6. }
    { exact HDN1. }
    { reflexivity. }
    { reflexivity. }
    { exact (proj1 Rd0). }
    { rewrite GNU. exact TNP. }
    { unfold loop. clear - NP1. lia. }
    { exact LOOP1. }
    { rewrite GNU. exact Edsn. }
    { rewrite GNU. exact HinsnU. }
    { rewrite GNU.
      apply (div_top_init (bn_buf bsn) (firstn tn (bn_buf bnum)) (firstn dn nbuf) sh dn tn nP).
      - exact OKp1.
      - rewrite <- TNP. exact OKp2.
      - exact HDN1.
      - exact NP1.
      - exact NP2.
      - exact SH.
      - exact LIMnum.
      - exact LENnum.
      - exact FNP.
      - apply limbs_firstn. exact LIMnb.
      - apply firstn_length_le. exact Lnb2.
      - rewrite nth_firstn. destruct (Nat.ltb_spec (dn - 1) dn) as [LT|GE]; [exact (proj1 Rd0) | exfalso; clear - GE HDN1; lia]. }
    { rewrite GVU. exact Edv. }
    { rewrite GVU. exact HinpvU. }
    { rewrite GVU. reflexivity. }
    { rewrite GVU. exact RD. }
    { exact UD. }
    { exact SH. }

  Qed.
End Proofs.
End WithCeiling0.
