(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnModel BnTree BnInv BnBridge BgState BgInv BgLib BgArith BgMont BgExp.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Import Layout Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnMem BnTac.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnArr.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require Import BnHeap W_small.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require BnRep.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU2 Require Import W_small3.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgRepU Require Import BgRepDefs BgRep BgLayer BgIface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnEU Require Import ExpKit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Rnd.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Ltac the_mi := lazymatch goal with H : mem_inv bgusegs _ |- _ => exact H end.
Ltac to_implM :=
  lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
    lazymatch E with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition BN_MOD_MUL : Z := 0x109378.
Definition BN_CTX_START : Z := 0x100c14.
Definition BN_CTX_GET : Z := 0x100e84.
Definition BN_CTX_END : Z := 0x100da4.
Definition BN_MUL : Z := 0x102690.
Definition BN_SQR : Z := 0x107374.
Definition BN_NNMOD : Z := 0x108af0.

Section Proofs.

  Variable CS : Z.
  Hypothesis CS16 : 16 <= CS.
  Definition BN_MOD_MUL_STACK : Z := 64 + CS.

  Hypothesis BN_CTX_start_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (ac : Z) (qc : bptr),
    bn_pre s bs m OW LB PL EA sp lo B errv CS -> tp = wz RATP -> pl_ctx PL = Some (ac, qc) -> a0 = wz ac ->
    implM bgusegs (interp (embed (BN_CTX_start (tree_ops bptr) bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA
               (fun _ _ OW' PL' _ => PL' = PL /\ forall q A n, In (q, A, n) OW -> In (q, A, n) OW'))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_CTX_START) fc None m (seg_rom bgusegs)).

  Hypothesis BN_CTX_get_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (ac : Z) (qc : bptr),
    bn_pre s bs m OW LB PL EA sp lo B errv CS -> tp = wz RATP -> pl_ctx PL = Some (ac, qc) -> a0 = wz ac ->
    implM bgusegs (interp (embed (BN_CTX_get (tree_ops bptr) bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA
               (fun r bs' OW' PL' a0' => PL' = PL /\ (exists i, r = RPool i) /\ (exists a, ref_at bs' OW' PL r a /\ a0' = wz a) /\ forall q A n, In (q, A, n) OW -> In (q, A, n) OW'))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_CTX_GET) fc None m (seg_rom bgusegs)).

  Hypothesis BN_CTX_end_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (ac : Z) (qc : bptr),
    bn_pre s bs m OW LB PL EA sp lo B errv CS -> tp = wz RATP -> pl_ctx PL = Some (ac, qc) -> a0 = wz ac ->
    implM bgusegs (interp (embed (BN_CTX_end (tree_ops bptr) bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (fun _ _ OW' PL' _ => PL' = PL /\ OW' = OW))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_CTX_END) fc None m (seg_rom bgusegs)).

  Hypothesis BN_sqr_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (rr rx : bnref) (ar ax ac : Z) (qc : bptr),
    bn_pre s bs m OW LB PL EA sp lo B errv CS -> tp = wz RATP -> bv_unsigned sp mod 16 = 0 ->
    ref_at bs OW PL rr ar -> ref_at bs OW PL rx ax -> hpl PL rr -> rx <> ROne -> pl_ctx PL = Some (ac, qc) ->
    a0 = wz ar -> a1 = wz ax -> a2 = wz ac ->
    implM bgusegs (interp (embed (BN_sqr (tree_ops bptr) rr rx bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_SQR) fc None m (seg_rom bgusegs)).

  Hypothesis BN_mul_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (rr rx ry : bnref) (ar ax ay ac : Z) (qc : bptr),
    bn_pre s bs m OW LB PL EA sp lo B errv CS -> tp = wz RATP ->
    ref_at bs OW PL rr ar -> ref_at bs OW PL rx ax -> ref_at bs OW PL ry ay -> hpl PL rr -> rx <> ROne -> ry <> ROne -> pl_ctx PL = Some (ac, qc) ->
    a0 = wz ar -> a1 = wz ax -> a2 = wz ay -> a3 = wz ac ->
    implM bgusegs (interp (embed (BN_mul (tree_ops bptr) rr rx ry bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_MUL) fc None m (seg_rom bgusegs)).

  Hypothesis BN_nnmod_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (rr rx rm : bnref) (ar ax am ac : Z) (qc : bptr),
    bn_pre s bs m OW LB PL EA sp lo B errv CS -> tp = wz RATP ->
    ref_at bs OW PL rr ar -> ref_at bs OW PL rx ax -> ref_at bs OW PL rm am -> hpl PL rr -> rx <> ROne -> rm <> ROne -> pl_ctx PL = Some (ac, qc) ->
    a0 = wz ar -> a1 = wz ax -> a2 = wz am -> a3 = wz ac ->
    implM bgusegs (interp (embed (BN_nnmod (tree_ops bptr) rr rx rm bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_NNMOD) fc None m (seg_rom bgusegs)).

  Lemma BN_mod_mul_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (rr ra_ rb rm : bnref) (arr ara arb arm ac : Z) (qc : bptr),
    bn_pre s bs m OW LB PL EA sp lo B errv BN_MOD_MUL_STACK -> tp = wz RATP -> bv_unsigned sp mod 16 = 0 ->
    ref_at bs OW PL rr arr -> ref_at bs OW PL ra_ ara -> ref_at bs OW PL rb arb -> ref_at bs OW PL rm arm ->
    hpl PL rr -> ra_ <> ROne -> rb <> ROne -> rm <> ROne -> pl_ctx PL = Some (ac, qc) ->
    a0 = wz arr -> a1 = wz ara -> a2 = wz arb -> a3 = wz arm -> a4 = wz ac ->
    implM bgusegs (interp (embed (BN_mod_mul (tree_ops bptr) rr ra_ rb rm bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_MOD_MUL) fc None m (seg_rom bgusegs)).
  Proof.
    intros until qc. intros (HEAP & LS & FROK & AUX & SPB & B63 & ST & CEIL & GLO & LO & ERR & MI) -> SP16 HAr HAa HAb HAm WRr NROa NROb NROm HPC -> -> -> -> ->.
    unfold BN_MOD_MUL_STACK, BN_MOD_MUL, GLOBALS_TOP, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.

    assert (AaR : 0 < ara < 2^64) by (pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK HAa NROa) as (X & Y & _); clear - X Y SPR; lia).
    assert (AbR : 0 < arb < 2^64) by (pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK HAb NROb) as (X & Y & _); clear - X Y SPR; lia).
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgusegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3346328 - 164) with 3346164 in ERR.
    assert (GLO' : GLOBALS_TOP <= lo) by exact GLO.

    unfold BN_mod_mul, bbind, bret. cbn [bind ret tree_ops tbind fst snd].
    unfold implM. iprefix.

    carve_frame 64%nat ST. do 16 step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HWL : Forall (w_lib bs OW PL lo (bv_unsigned sp)) [(bv_unsigned sp + -64, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
    assert (WOK : Forall (w_ok OW LB bs PL EA (bv_unsigned sp) []) [(bv_unsigned sp + -64, bv_unsigned sp)]) by (constructor; [apply w_stack; cbn; lia| constructor]).
    pose proof (lib_state_frame s LB _ _ [] bs m m1 OW PL EA _ HEAP LS MU WM FROK WOK) as LS1.
    lazymatch type of FR with rw_cells _ _ _ ?fr =>
      assert (ENV : kenv LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -64) s bs OW m fr s bs m1 OW)
    end.
    { unfold kenv. split; [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL)|].
      split; [apply (seg_auxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK AUX MU WM HWL SPB ltac:(lia)); exact GLO'|].
      split; [exact ST|]. split; [exists errv; unfold LX_ERRNO, RATP; exact ERR|]. split; [exact MI|].
      split; [apply (seg_lx_pres _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL); lia|].
      split; [reflexivity|]. split; [reflexivity|]. split; [apply refs_stable_refl|]. split; [exact FR| cbn; lia]. }
    assert (FBlo : lo <= bv_unsigned sp + -64) by lia.
    assert (FBsp : bv_unsigned sp + -64 <= bv_unsigned sp) by lia.
    assert (SPR2 : bv_unsigned sp < 2 ^ 64) by lia.
    pose proof (kenv_pre LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -64) s bs OW m CEIL GLO' FBlo FBsp SPB B63 SPR2 FROK) as KPRE.
    pose proof (kenv_post LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -64) s bs OW m CEIL GLO' FBlo FBsp FROK) as KPOST.
    pose proof (fun A => @bn_post_kpost _ _ LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -64) CEIL FBlo FBsp SPR2 A) as BPK.
    assert (LOF : lo <= bv_unsigned sp + -64 - CS) by lia.
    clear HEAP AUX ST ERR MI MU WM HWL WOK FR.

    destruct (KPRE _ _ _ _ _ CS ENV LS1 LOF) as (errv1 & PRE1).
    ihere. to_implM.
    eapply implM_embed_bind.
    { eapply BN_CTX_start_walk; [exact PRE1| reflexivity| exact HPC| reflexivity]. }
    cbv beta. intros [u1 bs1] st1 ms1 PO. apply BPK in PO; [|intros v b o p a [E _]; exact E].
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & OW2 & -> & KP & (_ & INCL2)).
    destruct (KPOST _ _ _ _ _ _ _ _ _ ENV KP) as (ENV2 & LS2). pose proof KP as RS2; apply kpost_refs in RS2.
    cbn [fst snd] in *. clear PRE1 KP ENV LS1.
    replace (ret_pc (Z_to_bv 64 1086396)) with (Z_to_bv 64 1086396) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

    unfold implM. iprefix. step. step.
    destruct (KPRE _ _ _ _ _ CS ENV2 LS2 LOF) as (errv2 & PRE2).
    ihere. to_implM.
    eapply implM_embed_bind.
    { eapply BN_CTX_get_walk; [exact PRE2| reflexivity| exact HPC| reflexivity]. }
    cbv beta. intros [t bs2] st2 ms2 PO. apply BPK in PO; [|intros v b o p a [E _]; exact E].
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m3 & OW3 & -> & KP & (_ & (ti & Et) & (at_ & HAt & ->) & INCL3)).
    destruct (KPOST _ _ _ _ _ _ _ _ _ ENV2 KP) as (ENV3 & LS3). pose proof KP as RS3; apply kpost_refs in RS3.
    cbn [fst snd] in *. clear PRE2 KP ENV2 LS2.
    replace (ret_pc (Z_to_bv 64 1086404)) with (Z_to_bv 64 1086404) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

    pose proof (refs_stable_trans _ _ _ _ _ _ RS2 RS3) as RS13.
    pose proof (ref_at_stable _ _ _ _ PL _ _ RS13 HAr) as HAr3. pose proof (ref_at_stable _ _ _ _ PL _ _ RS13 HAa) as HAa3.
    pose proof (ref_at_stable _ _ _ _ PL _ _ RS13 HAb) as HAb3. pose proof (ref_at_stable _ _ _ _ PL _ _ RS13 HAm) as HAm3.
    pose proof ENV3 as (HEAP3 & _). pose proof (RH_nodup_l _ _ _ _ HEAP3) as ND3. pose proof (lib_state_h_parts _ _ _ _ _ _ LS3) as PARTS3.
    assert (FROK3 : frames_ok PL (bv_unsigned sp + -64) B) by (eapply frames_ok_call; [exact FROK| exact CEIL| exact FBlo| exact FBsp]).
    assert (NROt : t <> ROne) by (rewrite Et; unfold RPool, ROne, NFIX; lia).
    pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP3 PARTS3 FROK3 HAt NROt) as (At0 & AtC & _).
    assert (AtR : 0 < at_ < 2^64) by (clear - At0 AtC SPR; lia). clear AtC.

    unfold implM. iprefix.
    step. if_cases KZ; rewrite ?unsigned_lit in KZ by (clear - AtR; lia); zify_cond KZ; [exfalso; clear - KZ AtR; lia| clear KZ].
    step. step.

    step. if_cases KE; rewrite ?unsigned_lit in KE by (clear - AaR AbR; lia); zify_cond KE.
    -
      assert (Eab : ra_ = rb).
      { destruct (Nat.eq_dec ra_ rb) as [E|NE]; [exact E| exfalso].
        pose proof (struct_disj st2 OW3 LB m3 HEAP3 bs2 PL EA _ _ PARTS3 FROK3 ra_ rb ara arb NE HAa3 HAb3) as D. clear - D KE. lia. }
      subst rb. rewrite Nat.eqb_refl.
      do 2 step.
      destruct (KPRE _ _ _ _ _ CS ENV3 LS3 LOF) as (errv3 & PRE3).
      ihere. to_implM.
      eapply implM_embed_bind.
      { eapply BN_sqr_walk; [exact PRE3| reflexivity| rewrite ?unsigned_lit by lia; clear - SP16; Z.div_mod_to_equations; lia| exact HAt| exact HAa3| rewrite Et; apply hpl_pool| exact NROa| exact HPC| reflexivity| reflexivity| reflexivity]. }
      cbv beta. intros [u4 bs4] st4 ms4 PO. apply BPK in PO; [|intros v b o p a [E _]; exact E].
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m4 & OW4 & -> & KP & (_ & ->)).
      destruct (KPOST _ _ _ _ _ _ _ _ _ ENV3 KP) as (ENV4 & LS4). pose proof KP as RS4; apply kpost_refs in RS4.
      cbn [fst snd] in *. clear PRE3 KP.
      replace (ret_pc (Z_to_bv 64 1086472)) with (Z_to_bv 64 1086472) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      unfold implM. iprefix. step. if_true.

      do 4 step. step.
      destruct (KPRE _ _ _ _ _ CS ENV4 LS4 LOF) as (errv4 & PRE4).
      pose proof (refs_stable_trans _ _ _ _ _ _ RS13 RS4) as RS14.
      ihere. to_implM.
      eapply implM_embed_bind.
      { eapply BN_nnmod_walk; [exact PRE4| reflexivity| exact (ref_at_stable _ _ _ _ PL _ _ RS14 HAr)| exact (ref_at_stable _ _ _ _ PL _ _ RS4 HAt)
          | exact (ref_at_stable _ _ _ _ PL _ _ RS14 HAm)| exact WRr| exact NROt| exact NROm| exact HPC| reflexivity| reflexivity| reflexivity| reflexivity]. }
      cbv beta. intros [u5 bs5] st5 ms5 PO. apply BPK in PO; [|intros v b o p a [E _]; exact E].
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m5 & OW5 & -> & KP & (_ & ->)).
      destruct (KPOST _ _ _ _ _ _ _ _ _ ENV4 KP) as (ENV5 & LS5). pose proof KP as RS5; apply kpost_refs in RS5.
      cbn [fst snd] in *. clear PRE4 KP.
      replace (ret_pc (Z_to_bv 64 1086456)) with (Z_to_bv 64 1086456) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

      unfold implM. iprefix. step. step. step. step.
      destruct (KPRE _ _ _ _ _ CS ENV5 LS5 LOF) as (errv5 & PRE5).
      ihere. to_implM.
      eapply implM_post_evt.
      { eapply BN_CTX_end_walk; [exact PRE5| reflexivity| exact HPC| reflexivity]. }
      cbv beta. intros [u6 bs6] st6 ms6 PO. apply BPK in PO; [|intros v b o p a [E _]; exact E].
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m6 & OW6 & -> & KP & (_ & EOW6)).
      destruct (KPOST _ _ _ _ _ _ _ _ _ ENV5 KP) as (ENV6 & LS6). pose proof KP as RS6; apply kpost_refs in RS6.
      cbn [fst snd] in *. clear PRE5 KP.
      replace (ret_pc (Z_to_bv 64 1086488)) with (Z_to_bv 64 1086488) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof (kenv_final LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -64) s bs OW m _ _ _ _ _ ENV6) as (F1 & F2 & STF & (errvF & F4) & F5 & F6 & F7 & F8 & F9 & FRF).

      step. do 8 step. release_frame FRF STF (bv_unsigned sp). step. step.
      apply evt_done. unfold bn_post. do 15 eexists. exists m6, OW6, PL, errvF. split; [reflexivity|]. cbn [fst snd].
      split; [exact F1|]. split; [exact LS6|]. split; [exact F2|]. split; [exact STF|]. split; [exact F4|]. split; [exact F5|].
      split; [exact F6|]. split; [exact F7|]. split; [exact F8|]. split; [eapply refs_stable_trans; [exact F9| exact RS6] || exact F9|]. split; reflexivity.
    -
      assert (NE : ra_ <> rb).
      { intros E. subst rb. pose proof (ref_at_fun _ _ _ _ _ _ ND3 HAa3 HAb3) as EA_. clear - EA_ KE. lia. }
      replace ((ra_ =? rb)%nat) with false by (symmetry; apply Nat.eqb_neq; exact NE).
      do 3 step.
      destruct (KPRE _ _ _ _ _ CS ENV3 LS3 LOF) as (errv3 & PRE3).
      ihere. to_implM.
      eapply implM_embed_bind.
      { eapply BN_mul_walk; [exact PRE3| reflexivity| exact HAt| exact HAa3| exact HAb3| rewrite Et; apply hpl_pool| exact NROa| exact NROb| exact HPC
          | reflexivity| reflexivity| reflexivity| reflexivity]. }
      cbv beta. intros [u4 bs4] st4 ms4 PO. apply BPK in PO; [|intros v b o p a [E _]; exact E].
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m4 & OW4 & -> & KP & (_ & ->)).
      destruct (KPOST _ _ _ _ _ _ _ _ _ ENV3 KP) as (ENV4 & LS4). pose proof KP as RS4; apply kpost_refs in RS4.
      cbn [fst snd] in *. clear PRE3 KP.
      replace (ret_pc (Z_to_bv 64 1086432)) with (Z_to_bv 64 1086432) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      unfold implM. iprefix. step. if_false.

      do 4 step. step.
      destruct (KPRE _ _ _ _ _ CS ENV4 LS4 LOF) as (errv4 & PRE4).
      pose proof (refs_stable_trans _ _ _ _ _ _ RS13 RS4) as RS14.
      ihere. to_implM.
      eapply implM_embed_bind.
      { eapply BN_nnmod_walk; [exact PRE4| reflexivity| exact (ref_at_stable _ _ _ _ PL _ _ RS14 HAr)| exact (ref_at_stable _ _ _ _ PL _ _ RS4 HAt)
          | exact (ref_at_stable _ _ _ _ PL _ _ RS14 HAm)| exact WRr| exact NROt| exact NROm| exact HPC| reflexivity| reflexivity| reflexivity| reflexivity]. }
      cbv beta. intros [u5 bs5] st5 ms5 PO. apply BPK in PO; [|intros v b o p a [E _]; exact E].
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m5 & OW5 & -> & KP & (_ & ->)).
      destruct (KPOST _ _ _ _ _ _ _ _ _ ENV4 KP) as (ENV5 & LS5). pose proof KP as RS5; apply kpost_refs in RS5.
      cbn [fst snd] in *. clear PRE4 KP.
      replace (ret_pc (Z_to_bv 64 1086456)) with (Z_to_bv 64 1086456) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

      unfold implM. iprefix. step. step. step. step.
      destruct (KPRE _ _ _ _ _ CS ENV5 LS5 LOF) as (errv5 & PRE5).
      ihere. to_implM.
      eapply implM_post_evt.
      { eapply BN_CTX_end_walk; [exact PRE5| reflexivity| exact HPC| reflexivity]. }
      cbv beta. intros [u6 bs6] st6 ms6 PO. apply BPK in PO; [|intros v b o p a [E _]; exact E].
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m6 & OW6 & -> & KP & (_ & EOW6)).
      destruct (KPOST _ _ _ _ _ _ _ _ _ ENV5 KP) as (ENV6 & LS6). pose proof KP as RS6; apply kpost_refs in RS6.
      cbn [fst snd] in *. clear PRE5 KP.
      replace (ret_pc (Z_to_bv 64 1086488)) with (Z_to_bv 64 1086488) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof (kenv_final LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -64) s bs OW m _ _ _ _ _ ENV6) as (F1 & F2 & STF & (errvF & F4) & F5 & F6 & F7 & F8 & F9 & FRF).

      step. do 8 step. release_frame FRF STF (bv_unsigned sp). step. step.
      apply evt_done. unfold bn_post. do 15 eexists. exists m6, OW6, PL, errvF. split; [reflexivity|]. cbn [fst snd].
      split; [exact F1|]. split; [exact LS6|]. split; [exact F2|]. split; [exact STF|]. split; [exact F4|]. split; [exact F5|].
      split; [exact F6|]. split; [exact F7|]. split; [exact F8|]. split; [eapply refs_stable_trans; [exact F9| exact RS6] || exact F9|]. split; reflexivity.
  Qed.
End Proofs.
End WithCeiling0.
