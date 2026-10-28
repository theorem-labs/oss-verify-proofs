(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BnModel BnTree BnInv BnSpecs BnMInv BnBridge BgState BgInv BgLib.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Import Layout Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnMem BnCmp.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnWU Require Import WU_cmp_words.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnArr.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require Import BnHeap.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnAU Require Import BnAKit W_ucmp W_bncmp.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require BnRep.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgRepU Require Import BgRepDefs BgRep BgLayer BgIface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnRU Require Import BnRKit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition BN_UCMP_STACK : Z := 80.

Definition int_res (bs : bstate bptr) (OW : list block) (PL : placement) : Z -> bstate bptr -> list block -> placement -> word -> Prop :=
  fun c bs' OW' PL' a0' => PL' = PL /\ a0' = Z_to_bv 64 c /\ -2147483648 < c < 2147483648 /\ bs' = bs /\ OW' = OW.

Lemma BN_ucmp_evt : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
    (lo B : Z) (errv : word) (r1 r2 : bnref) (a b : Z),
  bn_pre s bs m OW LB PL EA sp lo B errv BN_UCMP_STACK -> tp = wz RATP ->
  ref_at bs OW PL r1 a -> ref_at bs OW PL r2 b -> r1 <> ROne -> r2 <> ROne -> a0 = wz a -> a1 = wz b ->
  evt bgusegs (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (int_res bs OW PL)
                     (ucmp_pure (getbn r1 bs) (getbn r2 bs), bs) s)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_UCMP_U) fc None m (seg_rom bgusegs)).
Proof.
  intros until b. intros PRE -> HA HB N1 N2 -> ->.
  pose proof PRE as (HEAP & LS & FROK & AUX & SPB & B63 & ST & CEIL & GLO & LO & ERR & MI).
  unfold BN_UCMP_STACK, GLOBALS_TOP in *.
  destruct (open_ro_u s OW LB m bs PL EA (bv_unsigned sp) B r1 a HEAP LS FROK HA N1) as (Da & SA & OKA' & UA & A0 & AC & DA0 & DAC & ALA & UPA).
  destruct (open_ro_u s OW LB m bs PL EA (bv_unsigned sp) B r2 b HEAP LS FROK HB N2) as (Db & SB & OKB' & UB & B0 & BC & DB0 & DBC & ALB & UPB).
  pose proof (bg_okm _ OKA') as OKA. pose proof (bg_okm _ OKB') as OKB.
  pose proof OKA as (_ & TDA & _). pose proof OKB as (_ & TDB & _).
  eapply evt_mono.
  { eapply (BN_ucmp_uspec ra sp gp (wz RATP) t0 t1 t2 s0 s1 (wz a) (wz b)) with (lo := lo) (A := a) (B := b) (Da := Da) (Db := Db)
      (ba := getbn r1 bs) (bb := getbn r2 bs);
      [exact SA | exact SB | apply limbs_at_firstn; exact UA | apply limbs_at_firstn; exact UB | exact OKA | exact OKB
      | exact A0 | exact B0 | exact ALA | exact ALB | exact UPA | exact UPB | exact ST | lia | lia | lia | unfold bn_dmax in *; lia | unfold bn_dmax in *; lia | exact MI | reflexivity | reflexivity]. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & ST').
  eapply (bn_post_silent ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m m' PL EA (int_res bs OW PL))
    with (W := [(bv_unsigned sp - 80, bv_unsigned sp)]) (errv := errv) (errv' := errv) (stack := 80);
    [exact PRE | lia | exact MU | exact WM | | | exact ST' | | exact MI' | ].
  - constructor; [apply w_stack; cbn; lia | constructor].
  - constructor; [left; cbn; lia | constructor].
  - eapply rw_cells_transport; [exact ERR | exact MU | exact WM |]. unfold LX_ERRNO, RATP. cbn. lia.
  - unfold int_res. split; [reflexivity|]. split; [reflexivity|]. split; [apply ucmp_pure_range; assumption|]. split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma BN_ucmp_walk : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
    (lo B : Z) (errv : word) (r1 r2 : bnref) (a b : Z),
  bn_pre s bs m OW LB PL EA sp lo B errv BN_UCMP_STACK -> tp = wz RATP ->
  ref_at bs OW PL r1 a -> ref_at bs OW PL r2 b -> r1 <> ROne -> r2 <> ROne -> a0 = wz a -> a1 = wz b ->
  implM bgusegs (interp (embed (BN_ucmp (tree_ops bptr) r1 r2 bs))) s
    (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA
             (fun c bs' OW' PL' a0' => int_res bs OW PL c bs' OW' PL' a0' /\ c = ucmp_pure (getbn r1 bs) (getbn r2 bs)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz BN_UCMP_U) fc None m (seg_rom bgusegs)).
Proof.
  intros until b. intros PRE Etp HA HB N1 N2 E0 E1.
  pose proof PRE as (HEAP & LS & FROK & _).
  destruct (open_ro s OW LB m bs PL EA (bv_unsigned sp) B r1 a HEAP LS FROK HA N1) as (_ & _ & (_ & _ & _ & FLA) & _).
  destruct (open_ro s OW LB m bs PL EA (bv_unsigned sp) B r2 b HEAP LS FROK HB N2) as (_ & _ & (_ & _ & _ & FLB) & _).
  unfold BN_ucmp, bbind, bget, bret, bunr. cbn [bind ret unreachable tree_ops tbind fst snd].
  assert (EL4A : Z.land (bn_flags (getbn r1 bs)) BN_FLG_CONSTTIME = 0) by (destruct FLA as [E|E]; rewrite E; reflexivity).
  assert (EL4B : Z.land (bn_flags (getbn r2 bs)) BN_FLG_CONSTTIME = 0) by (destruct FLB as [E|E]; rewrite E; reflexivity).
  unfold has_flag. rewrite EL4A, EL4B. cbn [Z.eqb negb orb embed interp].
  apply implM_interp_ret.
  eapply evt_mono; [eapply (BN_ucmp_evt ra sp gp tp t0 t1 t2 s0 s1 a0 a1) with (r1 := r1) (r2 := r2); eassumption|].
  intros ms' PO. unfold bn_post in *. cbn [fst snd] in *.
  destruct PO as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & m' & OW' & PL' & errv' & -> & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11).
  do 15 eexists. exists m', OW', PL', errv'. split; [reflexivity|].
  do 10 (split; [assumption|]). split; [exact P11 | reflexivity].
Qed.

(* [comment removed for export] *)
Definition BN_CMP_STACK : Z := 16.

Lemma BN_cmp_evt : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
    (lo B : Z) (errv : word) (r1 r2 : bnref) (a b : Z),
  bn_pre s bs m OW LB PL EA sp lo B errv BN_CMP_STACK -> tp = wz RATP ->
  ref_at bs OW PL r1 a -> ref_at bs OW PL r2 b -> r1 <> ROne -> r2 <> ROne -> a0 = wz a -> a1 = wz b ->
  evt bgusegs (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (int_res bs OW PL)
                     (cmp_pure (getbn r1 bs) (getbn r2 bs), bs) s)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_CMP_U) fc None m (seg_rom bgusegs)).
Proof.
  intros until b. intros PRE -> HA HB N1 N2 -> ->.
  pose proof PRE as (HEAP & LS & FROK & AUX & SPB & B63 & ST & CEIL & GLO & LO & ERR & MI).
  unfold BN_CMP_STACK, GLOBALS_TOP in *.
  destruct (open_ro_u s OW LB m bs PL EA (bv_unsigned sp) B r1 a HEAP LS FROK HA N1) as (Da & SA & OKA' & UA & A0 & AC & DA0 & DAC & ALA & UPA).
  destruct (open_ro_u s OW LB m bs PL EA (bv_unsigned sp) B r2 b HEAP LS FROK HB N2) as (Db & SB & OKB' & UB & B0 & BC & DB0 & DBC & ALB & UPB).
  pose proof (bg_okm _ OKA') as OKA. pose proof (bg_okm _ OKB') as OKB.
  pose proof OKA as (_ & TDA & _). pose proof OKB as (_ & TDB & _).
  eapply evt_mono.
  { eapply (BN_cmp_uspec ra sp gp (wz RATP) t0 t1 t2 s0 s1 (wz a) (wz b)) with (lo := lo) (A := a) (B := b) (Da := Da) (Db := Db)
      (ba := getbn r1 bs) (bb := getbn r2 bs);
      [exact SA | exact SB | apply limbs_at_firstn; exact UA | apply limbs_at_firstn; exact UB | exact OKA | exact OKB
      | exact A0 | exact B0 | exact ALA | exact ALB | exact UPA | exact UPB | exact ST | lia | lia | lia | unfold bn_dmax in *; lia | unfold bn_dmax in *; lia | exact MI | reflexivity | reflexivity]. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & ST').
  eapply (bn_post_silent ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m m' PL EA (int_res bs OW PL))
    with (W := [(bv_unsigned sp - 16, bv_unsigned sp)]) (errv := errv) (errv' := errv) (stack := 16);
    [exact PRE | lia | exact MU | exact WM | | | exact ST' | | exact MI' | ].
  - constructor; [apply w_stack; cbn; lia | constructor].
  - constructor; [left; cbn; lia | constructor].
  - eapply rw_cells_transport; [exact ERR | exact MU | exact WM |]. unfold LX_ERRNO, RATP. cbn. lia.
  - unfold int_res. split; [reflexivity|]. split; [reflexivity|]. split; [pose proof (cmp_pure_range (getbn r1 bs) (getbn r2 bs)); lia|]. split; reflexivity.
Qed.

End WithCeiling0.
