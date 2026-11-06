(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import Tac ImageA ZBridge RzCPS.
From OSSVerify.Proofs.openssl.bndiv.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import Malloc Prog BnBase BnWords BnModel BnTree BnInv BnSpecs BnMInv.
From OSSVerify.Proofs.openssl.bndiv.lib.A Require Import Layout Shadow RT_iface D_defs.
From OSSVerify.Proofs.openssl.bndiv.lib.BnW Require Import BnTac BnMem BnCmp.
From OSSVerify.Proofs.openssl.bndiv.lib.BnW Require W_cmp_words.
From OSSVerify.Proofs.openssl.bndiv.lib.BnP Require Import BnKit BnKit2 BnArr.
From OSSVerify.Proofs.openssl.bndiv.lib.BnA Require BnAKit.
From OSSVerify.Proofs.openssl.bndiv.lib.BnAsan Require Import AsKit AsLoop LibKitA ARun BnHeapA BnRepDefs BnRepA ImplA BnIfaceA AsStruct BnAKitA W_ucmpA W_bncmpA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section WithRT.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Definition BN_UCMP_STACK : Z := 48.
Definition BN_CMP_STACK : Z := 16.

(* [comment removed for export] *)
Definition int_res (ls : lstate bptr) (OW : list block) : Z -> lstate bptr -> list block -> word -> Prop :=
  fun c ls' OW' a0' => a0' = Z_to_bv 64 c /\ -2147483648 < c < 2147483648 /\ ls' = ls /\ OW' = OW.

Lemma BN_ucmp_evtA : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : lstate bptr) (OW LB : list block) (AD : bn_addrs) (EA : err_addrs)
    (lo : Z) (r1 r2 : bnref) (a b : Z),
  bn_preA Σ ls m OW LB AD EA sp lo BN_UCMP_STACK 0 -> tp = wz TP_A ->
  ref_at ls OW AD r1 a -> ref_at ls OW AD r2 b -> a0 = wz a -> a1 = wz b ->
  evt asegs (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m AD EA 0 (int_res ls OW)
                      (ucmp_pure (getbn r1 ls) (getbn r2 ls), ls) Σ)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_UCMP) fc None m (seg_rom asegs)).
Proof.
  intros until b. intros PRE -> HA HB -> ->.
  pose proof PRE as (HEAP & LS & ST & CEIL & LO & SPT & SP16 & MI & CNT & CRED).
  unfold BN_UCMP_STACK in *.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3).
  destruct (open_ro_sh Σ OW LB m ls AD EA r1 a HEAP LS HA) as (Da & SA & OKA & UA & A0 & AC & DA0 & DAC & ACA & ALA & ACDA & ALDA).
  destruct (open_ro_sh Σ OW LB m ls AD EA r2 b HEAP LS HB) as (Db & SB & OKB & UB & B0 & BC & DB0 & DBC & ACB & ALB & ACDB & ALDB).
  pose proof OKA as (_ & TDA & _). pose proof OKB as (_ & TDB & _).
  eapply evt_mono.
  { eapply (BN_ucmp_specA ra sp gp (wz TP_A) t0 t1 t2 s0 s1 (wz a) (wz b)) with (lo := lo) (A := a) (B := b) (Da := Da) (Db := Db)
      (ba := getbn r1 ls) (bb := getbn r2 ls);
      [exact OKA | exact OKB | exact A0 | exact B0 | lia | lia | lia | unfold bn_dmax in *; lia | unfold bn_dmax in *; lia
      | exact ALA | exact ALB | exact ALDA | exact ALDB | lia
      | exact SA | exact SB | apply limbs_at_firstn; exact UA | apply limbs_at_firstn; exact UB | exact ST | exact MI
      | exact (AH_shb _ _ _ _ HEAP) | exact ACA | exact ACB | exact ACDA | exact ACDB | reflexivity | reflexivity]. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & ST').
  eapply (bn_post_silentA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Σ ls OW LB lo m m' AD EA 0 (int_res ls OW))
    with (W := [(bv_unsigned sp - 48, bv_unsigned sp)]) (stack := 48);
    [exact PRE | lia | lia | exact MU | exact WM | | | exact ST' | exact MI' | ].
  - constructor; [apply w_stack; cbn; lia | constructor].
  - constructor; [left; cbn; lia | constructor].
  - unfold int_res. split; [reflexivity|]. split; [apply BnAKit.ucmp_pure_range; assumption|]. split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma BN_ucmp_walkA : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : lstate bptr) (OW LB : list block) (AD : bn_addrs) (EA : err_addrs)
    (lo : Z) (r1 r2 : bnref) (a b : Z),
  bn_preA Σ ls m OW LB AD EA sp lo BN_UCMP_STACK 0 -> tp = wz TP_A ->
  ref_at ls OW AD r1 a -> ref_at ls OW AD r2 b -> a0 = wz a -> a1 = wz b ->
  implA (BN_ucmp (tree_ops bptr) r1 r2 ls) Σ
    (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m AD EA 0
              (fun c ls' OW' a0' => int_res ls OW c ls' OW' a0' /\ c = ucmp_pure (getbn r1 ls) (getbn r2 ls)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz BN_UCMP) fc None m (seg_rom asegs)).
Proof.
  intros until b. intros PRE Etp HA HB E0 E1.
  pose proof PRE as (HEAP & LS & _).
  destruct (open_ro Σ OW LB m ls AD EA r1 a HEAP LS HA) as (_ & _ & (_ & _ & _ & FLA) & _).
  destruct (open_ro Σ OW LB m ls AD EA r2 b HEAP LS HB) as (_ & _ & (_ & _ & _ & FLB) & _).
  unfold BN_ucmp, bbind, bget, bret, bunr. cbn [bind ret unreachable tree_ops tbind fst snd].
  assert (EL4A : Z.land (bn_flags (getbn r1 ls)) BN_FLG_CONSTTIME = 0) by (destruct FLA as [E|E]; rewrite E; reflexivity).
  assert (EL4B : Z.land (bn_flags (getbn r2 ls)) BN_FLG_CONSTTIME = 0) by (destruct FLB as [E|E]; rewrite E; reflexivity).
  rewrite EL4A, EL4B. cbn [Z.eqb negb orb].
  apply implA_ret_evt.
  eapply evt_mono; [eapply (BN_ucmp_evtA ra sp gp tp t0 t1 t2 s0 s1 a0 a1) with (r1 := r1) (r2 := r2); eassumption|].
  intros ms' PO. unfold bn_postA in *. cbn [fst snd] in *.
  destruct PO as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & F' & fc' & m' & OW' & -> & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9).
  do 17 eexists. exists m', OW'. split; [reflexivity|].
  do 8 (split; [assumption|]). split; [exact P9 | reflexivity].
Qed.

Lemma BN_cmp_evtA : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : lstate bptr) (OW LB : list block) (AD : bn_addrs) (EA : err_addrs)
    (lo : Z) (r1 r2 : bnref) (a b : Z),
  bn_preA Σ ls m OW LB AD EA sp lo BN_CMP_STACK 0 -> tp = wz TP_A ->
  ref_at ls OW AD r1 a -> ref_at ls OW AD r2 b -> a0 = wz a -> a1 = wz b ->
  evt asegs (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m AD EA 0 (int_res ls OW)
                      (cmp_pure (getbn r1 ls) (getbn r2 ls), ls) Σ)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_CMP) fc None m (seg_rom asegs)).
Proof.
  intros until b. intros PRE -> HA HB -> ->.
  pose proof PRE as (HEAP & LS & ST & CEIL & LO & SPT & SP16 & MI & CNT & CRED).
  unfold BN_CMP_STACK in *.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3).
  destruct (open_ro_sh Σ OW LB m ls AD EA r1 a HEAP LS HA) as (Da & SA & OKA & UA & A0 & AC & DA0 & DAC & ACA & ALA & ACDA & ALDA).
  destruct (open_ro_sh Σ OW LB m ls AD EA r2 b HEAP LS HB) as (Db & SB & OKB & UB & B0 & BC & DB0 & DBC & ACB & ALB & ACDB & ALDB).
  pose proof OKA as (_ & TDA & _). pose proof OKB as (_ & TDB & _).
  eapply evt_mono.
  { eapply (BN_cmp_specA ra sp gp (wz TP_A) t0 t1 t2 s0 s1 (wz a) (wz b)) with (lo := lo) (A := a) (B := b) (Da := Da) (Db := Db)
      (ba := getbn r1 ls) (bb := getbn r2 ls);
      [exact OKA | exact OKB | exact A0 | exact B0 | lia | lia | lia | unfold bn_dmax in *; lia | unfold bn_dmax in *; lia
      | exact ALA | exact ALB | exact ALDA | exact ALDB | lia
      | exact SA | exact SB | apply limbs_at_firstn; exact UA | apply limbs_at_firstn; exact UB | exact ST | exact MI
      | exact (AH_shb _ _ _ _ HEAP) | exact ACA | exact ACB | exact ACDA | exact ACDB | reflexivity | reflexivity]. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & ST').
  eapply (bn_post_silentA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Σ ls OW LB lo m m' AD EA 0 (int_res ls OW))
    with (W := [(bv_unsigned sp - 16, bv_unsigned sp)]) (stack := 16);
    [exact PRE | lia | lia | exact MU | exact WM | | | exact ST' | exact MI' | ].
  - constructor; [apply w_stack; cbn; lia | constructor].
  - constructor; [left; cbn; lia | constructor].
  - unfold int_res. split; [reflexivity|]. split; [pose proof (BnAKit.cmp_pure_range (getbn r1 ls) (getbn r2 ls)); lia|]. split; reflexivity.
Qed.

End WithRT.
