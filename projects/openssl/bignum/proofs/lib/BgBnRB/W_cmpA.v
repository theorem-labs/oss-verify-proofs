(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac ZBridge RzCPS. 
From OSSVerify.Proofs.openssl.bignum.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Malloc Prog BnBase BnWords BnModel BnTree BnInv BnSpecs BnMInv BgState BgInv BgLib.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgB Require Import Layout RT_iface D_defs.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnMem BnCmp.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnW Require W_cmp_words.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnA Require BnAKit.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import AsKit AsLoop.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require Import LibKitA ARun BnHeapA ImplA AsStruct W_ucmpA W_bncmpA.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require BnRepDefs BnRepA BnIfaceA.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepB Require Import BgRepDefs BgRep BgLayer BgIface.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require Import BnAKitA.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import UbKit.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require Import UbStruct.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Definition ub_kind (pc : Z) : Z :=
  match pc with
  | 2243880 => 1
  | 2243884 => 2
  | 2243916 => 1
  | 2243920 => 2
  | 2244064 => 1
  | 2244068 => 2
  | 2244084 => 2
  | 2244092 => 1
  | 2244096 => 1
  | 2244112 => 2
  | 2244116 => 1
  | 2244120 => 1
  | 2244124 => 2
  | 2244128 => 2
  | 2244132 => 1
  | 2244136 => 2
  | 2244160 => 2
  | 2244164 => 1
  | 2244168 => 1
  | 2244172 => 2
  | 2244176 => 2
  | 2244180 => 1
  | 2244184 => 2
  | 2244312 => 1
  | 2244316 => 1
  | 2244320 => 1
  | 2244324 => 1
  | 2244344 => 2
  | 2244348 => 1
  | 2244352 => 1
  | 2244356 => 2
  | 2244360 => 2
  | 2244380 => 2
  | 2244384 => 1
  | 2244388 => 1
  | 2244392 => 2
  | 2244396 => 2
  | 2244584 => 1
  | 2244588 => 2
  | 2244592 => 1
  | 2244596 => 1
  | 2244600 => 1
  | 2244604 => 1
  | 2244608 => 2
  | 2244612 => 2
  | 2244724 => 1
  | 2244728 => 2
  | 2244732 => 1
  | 2244736 => 1
  | 2244740 => 1
  | 2244744 => 1
  | 2244748 => 2
  | 2244752 => 2
  | 2245100 => 1
  | 2245104 => 1
  | 2245108 => 2
  | 2245300 => 2
  | 2245332 => 1
  | 2245352 => 2
  | 2245356 => 1
  | 2245360 => 1
  | 2245364 => 2
  | 2245368 => 2
  | 2245372 => 1
  | 2245376 => 2
  | 2245412 => 2
  | 2245416 => 1
  | 2245420 => 1
  | 2245424 => 1
  | 2245428 => 2
  | 2245432 => 2
  | 2245436 => 1
  | 2245440 => 2
  | _ => 0
  end%Z.
Ltac ub := repeat (ub1 ub_kind).
Local Ltac ub_unfold ::= unfold BnHeapA.ACEIL in *.
Open Scope Z_scope.

Section WithRT.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Definition BN_UCMP_STACK : Z := 80.
Definition BN_CMP_STACK : Z := 16.

Definition int_res (ls : bstate bptr) (OW : list block) (PL : placement) : Z -> bstate bptr -> list block -> placement -> word -> Prop :=
  fun c ls' OW' PL' a0' => PL' = PL /\ a0' = Z_to_bv 64 c /\ -2147483648 < c < 2147483648 /\ ls' = ls /\ OW' = OW.

Lemma BN_cmp_evtA : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
    (lo : Z) (r1 r2 : bnref) (a b : Z),
  bn_preA Σ ls m OW LB PL EA sp lo BN_CMP_STACK 0 -> tp = wz TP_A ->
  ref_at ls OW PL r1 a -> ref_at ls OW PL r2 b -> r1 <> ROne -> r2 <> ROne -> a0 = wz a -> a1 = wz b ->
  evt bgbsegs (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA 0 (int_res ls OW PL)
                      (cmp_pure (getbn r1 ls) (getbn r2 ls), ls) Σ)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_CMP) fc None m (seg_rom bgbsegs)).
Proof.
  intros until b. intros PRE -> HA HB N1 N2 -> ->. change (not_one r1) in N1. change (not_one r2) in N2.
  pose proof PRE as (HEAP & LS & FROK & ST & CEIL & LO & SPT & SP16 & MI & CNT & CRED & FAL & NOFR).
  unfold BN_CMP_STACK in *.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3).
  destruct (open_ro_shu Σ OW LB m ls PL EA _ r1 a HEAP LS FROK NOFR HA N1) as (Da & SA & OKA' & UA & A0 & AC & DA0 & DAC & ACA & ALA & ACDA & ALDA & UDA & _).
  destruct (open_ro_shu Σ OW LB m ls PL EA _ r2 b HEAP LS FROK NOFR HB N2) as (Db & SB & OKB' & UB & B0 & BC & DB0 & DBC & ACB & ALB & ACDB & ALDB & UDB & _).
  pose proof (bg_okm _ OKA') as OKA. pose proof (bg_okm _ OKB') as OKB.
  pose proof OKA as (_ & TDA & _). pose proof OKB as (_ & TDB & _).
  eapply evt_mono.
  { eapply (BN_cmp_specA ra sp gp (wz TP_A) t0 t1 t2 s0 s1 (wz a) (wz b)) with (lo := lo) (A := a) (B := b) (Da := Da) (Db := Db)
      (ba := getbn r1 ls) (bb := getbn r2 ls);
      [exact OKA | exact OKB | exact A0 | exact B0 | lia | lia | lia | unfold bn_dmax in *; lia | unfold bn_dmax in *; lia
      | exact ALA | exact ALB | exact ALDA | exact ALDB | lia
      | exact SA | exact SB | apply limbs_at_firstn; exact UA | apply limbs_at_firstn; exact UB | exact ST | exact MI
      | exact (AH_shb _ _ _ _ HEAP) | exact ACA | exact ACB | exact ACDA | exact ACDB | reflexivity | reflexivity | exact UDA | exact UDB]. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & ST').
  eapply (bn_post_silentA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Σ ls OW LB lo m m' PL EA 0 (int_res ls OW PL))
    with (W := [(bv_unsigned sp - 16, bv_unsigned sp)]) (stack := 16);
    [exact PRE | lia | lia | exact MU | exact WM | | | exact ST' | exact MI' | ].
  - constructor; [apply w_stack; cbn; lia | constructor].
  - constructor; [left; cbn; lia | constructor].
  - unfold int_res. split; [reflexivity|]. split; [reflexivity|]. split; [pose proof (BnAKit.cmp_pure_range (getbn r1 ls) (getbn r2 ls)); lia|]. split; reflexivity.
Qed.

End WithRT.
