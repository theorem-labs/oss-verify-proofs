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
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnWU Require Import BnUTac.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnArr.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require Import BnHeap W_small BnUKit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require BnRep.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU2 Require Import W_small3.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgRepU Require Import BgRepDefs BgRep BgLayer BgIface BnUAlign.
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

Definition BN_NNMOD : Z := 0x108af0.
Definition BN_DIV : Z := 0x10966c.
Definition BN_ADD : Z := 0x10a744.
Definition BN_SUB : Z := 0x10ac14.

Section Proofs.

  Variable CS : Z.
  Hypothesis CS16 : 16 <= CS.
  Definition BN_NNMOD_STACK : Z := 32 + CS.

  Hypothesis BN_div_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (rr rx rm : bnref) (ar ax am ac : Z) (qc : bptr),
    bn_pre s bs m OW LB PL EA sp lo B errv CS -> tp = wz RATP ->
    ref_at bs OW PL rr ar -> ref_at bs OW PL rx ax -> ref_at bs OW PL rm am -> hpl PL rr -> rx <> ROne -> rm <> ROne -> pl_ctx PL = Some (ac, qc) ->
    a0 = wz 0 -> a1 = wz ar -> a2 = wz ax -> a3 = wz am -> a4 = wz ac ->
    implM bgusegs (interp (embed (BN_div (tree_ops bptr) None (Some rr) rx rm bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_DIV) fc None m (seg_rom bgusegs)).

  Hypothesis BN_add_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (rr x y : bnref) (R X Y : Z),
    bn_pre s bs m OW LB PL EA sp lo B errv CS -> tp = wz RATP ->
    ref_at bs OW PL rr R -> hpl PL rr -> ref_at bs OW PL x X -> x <> ROne -> ref_at bs OW PL y Y -> y <> ROne ->
    a0 = wz R -> a1 = wz X -> a2 = wz Y ->
    implM bgusegs (interp (embed (BN_add (tree_ops bptr) rr x y bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_ADD) fc None m (seg_rom bgusegs)).

  Hypothesis BN_sub_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (rr x y : bnref) (R X Y : Z),
    bn_pre s bs m OW LB PL EA sp lo B errv CS -> tp = wz RATP ->
    ref_at bs OW PL rr R -> hpl PL rr -> ref_at bs OW PL x X -> x <> ROne -> ref_at bs OW PL y Y -> y <> ROne ->
    a0 = wz R -> a1 = wz X -> a2 = wz Y ->
    implM bgusegs (interp (embed (BN_sub (tree_ops bptr) rr x y bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_SUB) fc None m (seg_rom bgusegs)).

  Lemma BN_nnmod_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (rr rx rm : bnref) (ar ax am ac : Z) (qc : bptr),
    bn_pre s bs m OW LB PL EA sp lo B errv BN_NNMOD_STACK -> tp = wz RATP ->
    ref_at bs OW PL rr ar -> ref_at bs OW PL rx ax -> ref_at bs OW PL rm am -> hpl PL rr -> rx <> ROne -> rm <> ROne -> pl_ctx PL = Some (ac, qc) ->
    a0 = wz ar -> a1 = wz ax -> a2 = wz am -> a3 = wz ac ->
    implM bgusegs (interp (embed (BN_nnmod (tree_ops bptr) rr rx rm bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_NNMOD) fc None m (seg_rom bgusegs)).
  Proof.
    intros until qc. intros (HEAP & LS & FROK & AUX & SPB & B63 & ST & CEIL & GLO & LO & ERR & MI) -> HAr HAx HAm HPr NROx NROm HPC -> -> -> ->.
    pose proof (proj1 HPr) as NROr. pose proof (hpl_wref _ _ HPr) as WRr.
    unfold BN_NNMOD_STACK, BN_NNMOD, GLOBALS_TOP, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
    assert (ArR : 0 < ar < 2^64) by (pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK HAr NROr) as (X & Y & _); clear - X Y SPR; lia).
    assert (AmR : 0 < am < 2^64) by (pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK HAm NROm) as (X & Y & _); clear - X Y SPR; lia).
    pose proof (ref_at_ualign _ _ _ _ _ _ _ _ _ HEAP PARTS HAr NROr) as (_ & AR8).
    pose proof (ref_at_ualign _ _ _ _ _ _ _ _ _ HEAP PARTS HAm NROm) as (_ & AM8).
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgusegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3346328 - 164) with 3346164 in ERR.
    assert (GLO' : GLOBALS_TOP <= lo) by exact GLO.

    unfold BN_nnmod, BN_mod, bbind, bget, bret, bunr. cbn [bind ret unreachable tree_ops tbind fst snd].
    unfold implM. iprefix.

    carve_frame 32%nat ST. do 6 step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    step.
    step. if_cases KE; rewrite ?unsigned_lit in KE by (clear - ArR AmR; lia); zify_cond KE.
    {
      assert (Erm : rr = rm).
      { destruct (Nat.eq_dec rr rm) as [E|NE]; [exact E| exfalso].
        pose proof (struct_disj s OW LB m HEAP bs PL EA _ _ PARTS FROK rr rm ar am NE HAr HAm) as D. clear - D KE. lia. }
      replace ((rr =? rm)%nat) with true by (symmetry; apply Nat.eqb_eq; exact Erm).
      ihere. to_implM. cbn [embed interp]. apply implM_interp_unr. }
    assert (NErm : rr <> rm).
    { intros E. pose proof HAm as HAm'. rewrite <- E in HAm'. pose proof (ref_at_fun _ _ _ _ _ _ ND HAr HAm') as EA_. clear - EA_ KE. lia. }
    replace ((rr =? rm)%nat) with false by (symmetry; apply Nat.eqb_neq; exact NErm).

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
    pose proof (kenv_open LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -32) s bs OW m CEIL FROK) as KOPEN.
    assert (LOF : lo <= bv_unsigned sp + -32 - CS) by lia.
    clear HEAP AUX ST ERR MI MU WM HWL WOK FR LS.

    do 6 step. step.
    destruct (KPRE _ _ _ _ _ CS ENV LS1 LOF) as (errv1 & PRE1).
    ihere. to_implM.
    eapply implM_embed_bind.
    { eapply BN_div_walk; [exact PRE1| reflexivity| exact HAr| exact HAx| exact HAm| exact HPr| exact NROx| exact NROm| exact HPC
        | reflexivity| reflexivity| reflexivity| reflexivity| reflexivity]. }
    cbv beta. intros [u1 bs1] st1 ms1 PO. apply BPK in PO; [|intros v b o p a [E _]; exact E].
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & OW2 & -> & KP & (_ & ->)).
    destruct (KPOST _ _ _ _ _ _ _ _ _ ENV KP) as (ENV2 & LS2). pose proof KP as RS2; apply kpost_refs in RS2.
    cbn [fst snd] in *. clear PRE1 KP ENV LS1.
    replace (ret_pc (Z_to_bv 64 0x108b2c)) with (Z_to_bv 64 0x108b2c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (ref_at_stable _ _ _ _ PL _ _ RS2 HAr) as HAr2. pose proof (ref_at_stable _ _ _ _ PL _ _ RS2 HAm) as HAm2.
    unfold implM. iprefix. step. if_false.

    destruct (KOPEN _ _ _ _ _ rr ar ENV2 LS2 HAr2 NROr) as (Dr & BNr & _ & _ & _ & _ & _ & _).
    unfold bn_cells in BNr.
    chkw ltac:(fun C => clear - C ArR; lia).
    step. rewrite ?(land7_wrap _ AR8), ?(land7_wz _ AR8).
    chkw ltac:(fun C => clear - C; lia).
    step. clear BNr.
    destruct (bn_neg (getbn rr bs1)) eqn:ENr; cbn [Z.b2z negb]; cbv beta.
    2: {
         step. if_true.
         ihere. to_implM. cbn [embed interp]. apply implM_interp_ret.
         pose proof (kenv_final LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -32) s bs OW m _ _ _ _ _ ENV2) as (F1 & F2 & STF & (errvF & F4) & F5 & F6 & F7 & F8 & F9 & FRF).
         step. do 4 step. release_frame FRF STF (bv_unsigned sp). step. step.
         apply evt_done. unfold bn_post. do 15 eexists. exists m2, OW2, PL, errvF. split; [reflexivity|]. cbn [fst snd].
         split; [exact F1|]. split; [exact LS2|]. split; [exact F2|]. split; [exact STF|]. split; [exact F4|]. split; [exact F5|].
         split; [exact F6|]. split; [exact F7|]. split; [exact F8|]. split; [exact F9|]. split; reflexivity. }

    step. if_false.
    destruct (KOPEN _ _ _ _ _ rm am ENV2 LS2 HAm2 NROm) as (Dm & BNm & _ & _ & _ & _ & _ & _).
    unfold bn_cells in BNm.
    chkw ltac:(fun C => clear - C AmR; lia).
    step. rewrite ?(land7_wrap _ AM8), ?(land7_wz _ AM8).
    chkw ltac:(fun C => clear - C; lia).
    step. clear BNm.
    destruct (got_add_sub _ _ _ _ _ _ _ LS2) as (GA & GS). unfold GOT_BN_ADD, GOT_BN_SUB, MallocRep.wz in GA, GS.
    pose proof ENV2 as (_ & _ & ST2 & _ & _ & _ & _ & _ & _ & FR2 & _).
    pose proof (kenv_tail LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -32) s bs OW m CEIL GLO' FBlo FBsp SPB B63 SPR2 FROK
                _ _ _ m2 OW2 CS errv ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                (fun (_ : unit) (_ : bstate bptr) (_ : list block) (PL' : placement) (a0' : word) => PL' = PL /\ a0' = Z_to_bv 64 1)
                ENV2 LS2) as TAILK.
    destruct (bn_neg (getbn rm bs1)) eqn:ENm; cbn [Z.b2z].
    -
      step. if_false.
      step. step. step.
      step. step. step.
      do 4 step. release_frame FR2 ST2 (bv_unsigned sp). step. step.
      ihere. to_implM.
      destruct (TAILK ST2 ltac:(clear - LO; lia)) as [[errvX PREX] POSTX].
      rewrite Z_to_bv_bv_unsigned in PREX, POSTX.
      eapply implM_mono; [eapply BN_sub_walk; [exact PREX| reflexivity| exact HAr2| exact HPr| exact HAr2| exact NROr| exact HAm2| exact NROm| reflexivity| reflexivity| reflexivity]|].
      cbv beta. intros r st' ms' PO. apply POSTX. exact PO.
    -
      step. if_true.
      step. step.
      step. step. step.
      do 4 step. release_frame FR2 ST2 (bv_unsigned sp). step. step.
      ihere. to_implM.
      destruct (TAILK ST2 ltac:(clear - LO; lia)) as [[errvX PREX] POSTX].
      rewrite Z_to_bv_bv_unsigned in PREX, POSTX.
      eapply implM_mono; [eapply BN_add_walk; [exact PREX| reflexivity| exact HAr2| exact HPr| exact HAr2| exact NROr| exact HAm2| exact NROm| reflexivity| reflexivity| reflexivity]|].
      cbv beta. intros r st' ms' PO. apply POSTX. exact PO.
  Qed.
End Proofs.
End WithCeiling0.
