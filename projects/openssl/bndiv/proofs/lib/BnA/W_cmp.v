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
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import BnBase BnWords BnModel BnTree BnInv BnSpecs BnMInv BnBridge.
From OSSVerify.Proofs.openssl.bndiv.lib.P Require Import Layout Lib_iface Lib_kit.
From OSSVerify.Proofs.openssl.bndiv.lib.BnW Require Import BnMem BnCmp W_cmp_words.
From OSSVerify.Proofs.openssl.bndiv.lib.BnP Require Import BnKit BnHeap BnArr BnRep BnIface W_expand.
From OSSVerify.Proofs.openssl.bndiv.lib.BnA Require Import BnAKit W_ucmp W_bncmp.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.openssl.bndiv.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition BN_UCMP_STACK : Z := 32.

(* [comment removed for export] *)
Definition int_res (ls : lstate bptr) (OW : list block) : Z -> lstate bptr -> list block -> word -> Prop :=
  fun c ls' OW' a0' => a0' = Z_to_bv 64 c /\ -2147483648 < c < 2147483648 /\ ls' = ls /\ OW' = OW.

Lemma BN_ucmp_evt : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (ls : lstate bptr) (OW LB : list block) (AD : bn_addrs) (EA : err_addrs)
    (lo B : Z) (errv : word) (r1 r2 : bnref) (a b : Z),
  bn_pre s ls m OW LB AD EA sp lo B errv BN_UCMP_STACK -> tp = wz RATP ->
  ref_at ls OW AD r1 a -> ref_at ls OW AD r2 b -> a0 = wz a -> a1 = wz b ->
  evt psegs (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s ls OW LB lo B m AD EA (int_res ls OW)
                     (ucmp_pure (getbn r1 ls) (getbn r2 ls), ls) s)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_UCMP) fc None m (seg_rom psegs)).
Proof.
  intros until b. intros PRE -> HA HB -> ->.
  pose proof PRE as (HEAP & LS & AUX & SPB & ST & CEIL & GLO & LO & ERR & MI).
  unfold BN_UCMP_STACK, GLOBALS_TOP in *.
  destruct (open_ro s OW LB m ls AD EA r1 a HEAP LS HA) as (Da & SA & OKA & UA & A0 & AC & DA0 & DAC).
  destruct (open_ro s OW LB m ls AD EA r2 b HEAP LS HB) as (Db & SB & OKB & UB & B0 & BC & DB0 & DBC).
  pose proof OKA as (_ & TDA & _). pose proof OKB as (_ & TDB & _).
  eapply evt_mono.
  { eapply (BN_ucmp_spec ra sp gp (wz RATP) t0 t1 t2 s0 s1 (wz a) (wz b)) with (lo := lo) (A := a) (B := b) (Da := Da) (Db := Db)
      (ba := getbn r1 ls) (bb := getbn r2 ls);
      [exact SA | exact SB | apply limbs_at_firstn; exact UA | apply limbs_at_firstn; exact UB | exact OKA | exact OKB
      | exact A0 | exact B0 | exact ST | lia | lia | lia | unfold bn_dmax in *; lia | unfold bn_dmax in *; lia | exact MI | reflexivity | reflexivity]. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & ST').
  eapply (bn_post_silent ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s ls OW LB lo B m m' AD EA (int_res ls OW))
    with (W := [(bv_unsigned sp - 32, bv_unsigned sp)]) (errv := errv) (errv' := errv) (stack := 32);
    [exact PRE | lia | exact MU | exact WM | | | exact ST' | | exact MI' | ].
  - constructor; [apply w_stack; cbn; lia | constructor].
  - constructor; [left; cbn; lia | constructor].
  - eapply rw_cells_transport; [exact ERR | exact MU | exact WM |]. unfold LX_ERRNO, RATP. cbn. lia.
  - unfold int_res. split; [reflexivity|]. split; [apply ucmp_pure_range; assumption|]. split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma BN_ucmp_walk : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (ls : lstate bptr) (OW LB : list block) (AD : bn_addrs) (EA : err_addrs)
    (lo B : Z) (errv : word) (r1 r2 : bnref) (a b : Z),
  bn_pre s ls m OW LB AD EA sp lo B errv BN_UCMP_STACK -> tp = wz RATP ->
  ref_at ls OW AD r1 a -> ref_at ls OW AD r2 b -> a0 = wz a -> a1 = wz b ->
  implM psegs (interp (embed (BN_ucmp (tree_ops bptr) r1 r2 ls))) s
    (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s ls OW LB lo B m AD EA
             (fun c ls' OW' a0' => int_res ls OW c ls' OW' a0' /\ c = ucmp_pure (getbn r1 ls) (getbn r2 ls)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz BN_UCMP) fc None m (seg_rom psegs)).
Proof.
  intros until b. intros PRE Etp HA HB E0 E1.
  pose proof PRE as (HEAP & LS & _).
  destruct (open_ro s OW LB m ls AD EA r1 a HEAP LS HA) as (_ & _ & (_ & _ & _ & FLA) & _).
  destruct (open_ro s OW LB m ls AD EA r2 b HEAP LS HB) as (_ & _ & (_ & _ & _ & FLB) & _).
  unfold BN_ucmp, bbind, bget, bret, bunr. cbn [bind ret unreachable tree_ops tbind fst snd].
  assert (EL4A : Z.land (bn_flags (getbn r1 ls)) BN_FLG_CONSTTIME = 0) by (destruct FLA as [E|E]; rewrite E; reflexivity).
  assert (EL4B : Z.land (bn_flags (getbn r2 ls)) BN_FLG_CONSTTIME = 0) by (destruct FLB as [E|E]; rewrite E; reflexivity).
  rewrite EL4A, EL4B. cbn [Z.eqb negb orb embed interp].
  apply implM_interp_ret.
  eapply evt_mono; [eapply (BN_ucmp_evt ra sp gp tp t0 t1 t2 s0 s1 a0 a1) with (r1 := r1) (r2 := r2); eassumption|].
  intros ms' PO. unfold bn_post in *. cbn [fst snd] in *.
  destruct PO as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & m' & OW' & errv' & -> & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11).
  do 15 eexists. exists m', OW', errv'. split; [reflexivity|].
  do 10 (split; [assumption|]). split; [exact P11 | reflexivity].
Qed.

(* [comment removed for export] *)
Definition BN_CMP_STACK : Z := 16.

Lemma BN_cmp_evt : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (ls : lstate bptr) (OW LB : list block) (AD : bn_addrs) (EA : err_addrs)
    (lo B : Z) (errv : word) (r1 r2 : bnref) (a b : Z),
  bn_pre s ls m OW LB AD EA sp lo B errv BN_CMP_STACK -> tp = wz RATP ->
  ref_at ls OW AD r1 a -> ref_at ls OW AD r2 b -> a0 = wz a -> a1 = wz b ->
  evt psegs (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s ls OW LB lo B m AD EA (int_res ls OW)
                     (cmp_pure (getbn r1 ls) (getbn r2 ls), ls) s)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_CMP) fc None m (seg_rom psegs)).
Proof.
  intros until b. intros PRE -> HA HB -> ->.
  pose proof PRE as (HEAP & LS & AUX & SPB & ST & CEIL & GLO & LO & ERR & MI).
  unfold BN_CMP_STACK, GLOBALS_TOP in *.
  destruct (open_ro s OW LB m ls AD EA r1 a HEAP LS HA) as (Da & SA & OKA & UA & A0 & AC & DA0 & DAC).
  destruct (open_ro s OW LB m ls AD EA r2 b HEAP LS HB) as (Db & SB & OKB & UB & B0 & BC & DB0 & DBC).
  pose proof OKA as (_ & TDA & _). pose proof OKB as (_ & TDB & _).
  eapply evt_mono.
  { eapply (BN_cmp_spec ra sp gp (wz RATP) t0 t1 t2 s0 s1 (wz a) (wz b)) with (lo := lo) (A := a) (B := b) (Da := Da) (Db := Db)
      (ba := getbn r1 ls) (bb := getbn r2 ls);
      [exact SA | exact SB | apply limbs_at_firstn; exact UA | apply limbs_at_firstn; exact UB | exact OKA | exact OKB
      | exact A0 | exact B0 | exact ST | lia | lia | lia | unfold bn_dmax in *; lia | unfold bn_dmax in *; lia | exact MI | reflexivity | reflexivity]. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & ST').
  eapply (bn_post_silent ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s ls OW LB lo B m m' AD EA (int_res ls OW))
    with (W := [(bv_unsigned sp - 16, bv_unsigned sp)]) (errv := errv) (errv' := errv) (stack := 16);
    [exact PRE | lia | exact MU | exact WM | | | exact ST' | | exact MI' | ].
  - constructor; [apply w_stack; cbn; lia | constructor].
  - constructor; [left; cbn; lia | constructor].
  - eapply rw_cells_transport; [exact ERR | exact MU | exact WM |]. unfold LX_ERRNO, RATP. cbn. lia.
  - unfold int_res. split; [reflexivity|]. split; [pose proof (cmp_pure_range (getbn r1 ls) (getbn r2 ls)); lia|]. split; reflexivity.
Qed.

End WithCeiling0.
