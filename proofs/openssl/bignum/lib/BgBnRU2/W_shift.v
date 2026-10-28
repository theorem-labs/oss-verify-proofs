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
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Import Layout Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnMem BnTac BnTacX.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnArr.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require Import BnHeap W_small W_top.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require BnRep.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgRepU Require Import BgRepDefs BgRep BgLayer BgIface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnRU Require Import W_expand W_lshift W_rshift.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnEU Require Import ExpKit.
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

Definition BN_LSHIFT_W : Z := 0x10a1ec.
Definition BN_RSHIFT_W : Z := 0x10a4ec.
Definition BN_LSHIFT_W_STACK : Z := 32 + BN_LSHIFT_STACK.
Definition BN_RSHIFT_W_STACK : Z := 32 + BN_RSHIFT_STACK.
Definition RET1_L : Z := 0x10a210.  Definition RET2_L : Z := 0x10a21c.
Definition RET1_R : Z := 0x10a510.  Definition RET2_R : Z := 0x10a51c.

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Lemma BN_lshift_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (rr rx : bnref) (R X : Z) (n : Z),
    bn_pre s bs m OW LB PL EA sp lo B errv BN_LSHIFT_W_STACK -> tp = wz RATP ->
    ref_at bs OW PL rr R -> hpl PL rr -> ref_at bs OW PL rx X -> rx <> ROne ->
    a0 = wz R -> a1 = wz X -> a2 = wz n -> -2^31 <= n < 2^30 ->
    implM bgusegs (interp (embed (BN_lshift (tree_ops bptr) rr rx n bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (shift_res rr bs OW PL))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_LSHIFT_W) fc None m (seg_rom bgusegs)).
  Proof.
    intros until n. intros (HEAP & LS & FROK & AUX & SPB & B63 & ST & CEIL & GLO & LO & ERR & MI) -> HR HP HX NX -> -> -> HN.
    unfold BN_LSHIFT_W_STACK, BN_LSHIFT_W, GLOBALS_TOP, MallocRep.wz in *. unfold BN_LSHIFT_STACK, BN_WEXPAND_STACK, BN_EXPAND2_STACK in LO.
    change (2 ^ 31) with 2147483648 in HN. change (2 ^ 30) with 1073741824 in HN.

    unfold BN_lshift.
    destruct (Z.ltb_spec n 0) as [NNEG|NNEG].
    { unfold bunr. cbn [unreachable tree_ops embed]. apply implM_interp_unr. }
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgusegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3346328 - 164) with 3346164 in ERR.
    assert (GLO' : GLOBALS_TOP <= lo) by exact GLO.
    unfold bbind. cbn [bind tree_ops tbind fst snd].
    unfold implM. iprefix.

    carve_frame 32%nat ST. do 6 step.
    step. rewrite lts_signed by lia. destruct (Z.ltb_spec n 0) as [NN|_]; [exfalso; lia|].
    step.
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
    assert (LOF : lo <= bv_unsigned sp + -32 - BN_LSHIFT_STACK) by (unfold BN_LSHIFT_STACK, BN_WEXPAND_STACK, BN_EXPAND2_STACK; lia).
    clear HEAP AUX ST ERR MI MU WM HWL WOK FR.

    destruct (KPRE _ _ _ _ _ BN_LSHIFT_STACK ENV LS1 LOF) as (errv1 & PRE1).
    step.
    ihere. to_implM.
    eapply implM_embed_bind.
    { eapply (bn_lshift_fixed_top_walk HM HF) with (rr := rr) (rx := rx) (R := R) (X := X) (n := n);
        [exact PRE1 | reflexivity | exact HR | exact HP | exact HX | exact NX | reflexivity | reflexivity | reflexivity | lia]. }
    cbv beta. intros [u1 bs1] st1 ms1 PO. apply BPK in PO; [|intros v b o p a [E _]; exact E].
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & OW2 & -> & KP & (_ & -> & BST)).
    destruct (KPOST _ _ _ _ _ _ _ _ _ ENV KP) as (ENV2 & LS2). pose proof KP as RS2; apply kpost_refs in RS2.
    cbn [fst snd] in *. clear PRE1 KP ENV LS1.
    replace (ret_pc (Z_to_bv 64 RET1_L)) with (Z_to_bv 64 RET1_L) by (symmetry; apply ret_pc_even; [unfold RET1_L; lia| reflexivity]).
    pose proof (ref_at_stable _ _ _ _ PL _ _ RS2 HR) as HR2.

    unfold bbind, bget, bset. cbn [bind ret tree_ops tbind fst snd embed interp]. apply implM_interp_ret.
    unfold RET1_L. step. step. step.
    eapply (ctop_call LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -32) s bs OW m CEIL GLO' FBlo FBsp SPB B63 SPR2 FROK);
      [clear - LOF; unfold BN_LSHIFT_STACK, BN_WEXPAND_STACK, BN_EXPAND2_STACK in LOF; lia | exact ENV2 | exact LS2 | exact HR2 | exact (hpl_wref PL rr HP) |].
    intros m3 z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 ENV3 LS3.
    replace (ret_pc (Z_to_bv 64 RET2_L)) with (Z_to_bv 64 RET2_L) by (symmetry; apply ret_pc_even; [unfold RET2_L; lia| reflexivity]).
    pose proof (kenv_final LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -32) s bs OW m _ _ _ _ _ ENV3) as (F1 & F2 & STF & (errvF & F4) & F5 & F6 & F7 & F8 & F9 & FRF).
    unfold RET2_L. step. step. do 4 step. release_frame FRF STF (bv_unsigned sp). step. step.
    apply evt_done. unfold bn_post. do 15 eexists. exists m3, OW2, PL, errvF. split; [reflexivity|]. cbn [fst snd].
    split; [exact F1|]. split; [exact LS3|]. split; [exact F2|]. split; [exact STF|]. split; [exact F4|]. split; [exact F5|].
    split; [exact F6|]. split; [exact F7|]. split; [exact F8|]. split; [exact F9|].
    unfold shift_res. split; [reflexivity|]. split; [reflexivity| exact BST].
  Qed.

  Lemma BN_rshift_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (rr rx : bnref) (R X : Z) (n : Z),
    bn_pre s bs m OW LB PL EA sp lo B errv BN_RSHIFT_W_STACK -> tp = wz RATP ->
    ref_at bs OW PL rr R -> hpl PL rr -> ref_at bs OW PL rx X -> rx <> ROne ->
    a0 = wz R -> a1 = wz X -> a2 = wz n -> -2^31 <= n < 2^30 ->
    implM bgusegs (interp (embed (BN_rshift (tree_ops bptr) rr rx n bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (shift_res rr bs OW PL))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_RSHIFT_W) fc None m (seg_rom bgusegs)).
  Proof.
    intros until n. intros (HEAP & LS & FROK & AUX & SPB & B63 & ST & CEIL & GLO & LO & ERR & MI) -> HR HP HX NX -> -> -> HN.
    unfold BN_RSHIFT_W_STACK, BN_RSHIFT_W, GLOBALS_TOP, MallocRep.wz in *. unfold BN_RSHIFT_STACK, BN_WEXPAND_STACK, BN_EXPAND2_STACK in LO.
    change (2 ^ 31) with 2147483648 in HN. change (2 ^ 30) with 1073741824 in HN.

    unfold BN_rshift.
    destruct (Z.ltb_spec n 0) as [NNEG|NNEG].
    { unfold bunr. cbn [unreachable tree_ops embed]. apply implM_interp_unr. }
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgusegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3346328 - 164) with 3346164 in ERR.
    assert (GLO' : GLOBALS_TOP <= lo) by exact GLO.
    unfold bbind. cbn [bind tree_ops tbind fst snd].
    unfold implM. iprefix.

    carve_frame 32%nat ST. do 6 step.
    step. rewrite lts_signed by lia. destruct (Z.ltb_spec n 0) as [NN|_]; [exfalso; lia|].
    step.
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
    assert (LOF : lo <= bv_unsigned sp + -32 - BN_RSHIFT_STACK) by (unfold BN_RSHIFT_STACK, BN_WEXPAND_STACK, BN_EXPAND2_STACK; lia).
    clear HEAP AUX ST ERR MI MU WM HWL WOK FR.

    destruct (KPRE _ _ _ _ _ BN_RSHIFT_STACK ENV LS1 LOF) as (errv1 & PRE1).
    step.
    ihere. to_implM.
    eapply implM_embed_bind.
    { eapply (bn_rshift_fixed_top_walk HM HF) with (rr := rr) (rx := rx) (R := R) (X := X) (n := n);
        [exact PRE1 | reflexivity | exact HR | exact HP | exact HX | exact NX | reflexivity | reflexivity | reflexivity | lia]. }
    cbv beta. intros [u1 bs1] st1 ms1 PO. apply BPK in PO; [|intros v b o p a [E _]; exact E].
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & OW2 & -> & KP & (_ & -> & BST)).
    destruct (KPOST _ _ _ _ _ _ _ _ _ ENV KP) as (ENV2 & LS2). pose proof KP as RS2; apply kpost_refs in RS2.
    cbn [fst snd] in *. clear PRE1 KP ENV LS1.
    replace (ret_pc (Z_to_bv 64 RET1_R)) with (Z_to_bv 64 RET1_R) by (symmetry; apply ret_pc_even; [unfold RET1_R; lia| reflexivity]).
    pose proof (ref_at_stable _ _ _ _ PL _ _ RS2 HR) as HR2.

    unfold bbind, bget, bset. cbn [bind ret tree_ops tbind fst snd embed interp]. apply implM_interp_ret.
    unfold RET1_R. step. step. step.
    eapply (ctop_call LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -32) s bs OW m CEIL GLO' FBlo FBsp SPB B63 SPR2 FROK);
      [clear - LOF; unfold BN_RSHIFT_STACK, BN_WEXPAND_STACK, BN_EXPAND2_STACK in LOF; lia | exact ENV2 | exact LS2 | exact HR2 | exact (hpl_wref PL rr HP) |].
    intros m3 z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 ENV3 LS3.
    replace (ret_pc (Z_to_bv 64 RET2_R)) with (Z_to_bv 64 RET2_R) by (symmetry; apply ret_pc_even; [unfold RET2_R; lia| reflexivity]).
    pose proof (kenv_final LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -32) s bs OW m _ _ _ _ _ ENV3) as (F1 & F2 & STF & (errvF & F4) & F5 & F6 & F7 & F8 & F9 & FRF).
    unfold RET2_R. step. step. do 4 step. release_frame FRF STF (bv_unsigned sp). step. step.
    apply evt_done. unfold bn_post. do 15 eexists. exists m3, OW2, PL, errvF. split; [reflexivity|]. cbn [fst snd].
    split; [exact F1|]. split; [exact LS3|]. split; [exact F2|]. split; [exact STF|]. split; [exact F4|]. split; [exact F5|].
    split; [exact F6|]. split; [exact F7|]. split; [exact F8|]. split; [exact F9|].
    unfold shift_res. split; [reflexivity|]. split; [reflexivity| exact BST].
  Qed.

End Proofs.
End WithCeiling0.
