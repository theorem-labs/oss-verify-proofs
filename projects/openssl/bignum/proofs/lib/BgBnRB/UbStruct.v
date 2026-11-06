(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac ZBridge Arr. 
From OSSVerify.Proofs.openssl.bignum.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Malloc Prog BnBase BnWords BnModel BnTree BnInv BnSpecs BnMInv BgState BgInv BgLib.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgB Require Import Layout RT_iface D_defs.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnMem.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr.
From OSSVerify.Proofs.openssl.bignum.lib.BnWU Require Import BnUTac.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import AsKit AsLoop.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require Import LibKitA ARun BnHeapA AsStruct.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require BnRepDefs BnRepA BnIfaceA.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepB Require Import BgRepDefs BgRep BgLayer BgIface.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require Import BnAKitA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section WithRT.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Lemma arr_ubA : forall Σ OW LB m D (b : bignum bptr),
  AHEAP Σ OW LB m -> BnRepDefs.bn_arr m OW D b -> (0 < bn_dmax b)%nat -> 0 < D /\ D mod 16 = 0.
Proof.
  intros Σ OW LB m D b HEAP ARR HD. unfold BnRepDefs.bn_arr in ARR. destruct (bn_d b) as [p|] eqn:Ed.
  - destruct ARR as [Hin _]. pose proof (AH_range _ _ _ _ _ _ _ HEAP Hin) as (R0 & R16 & _). split; assumption.
  - destruct ARR as [_ Eb]. unfold bn_dmax in HD. rewrite Eb in HD. cbn in HD. lia.
Qed.

Lemma arr_ub_okA : forall Σ OW LB m D (b : bignum bptr) n,
  AHEAP Σ OW LB m -> BnRepDefs.bn_arr m OW D b -> n <= Z.of_nat (bn_dmax b) -> ub_ptr_ok n D.
Proof.
  intros Σ OW LB m D b n HEAP ARR Hn Hpos.
  destruct (arr_ubA Σ OW LB m D b HEAP ARR ltac:(lia)) as (H0 & H16). split; [exact H0|]. clear - H16. Z.div_mod_to_equations. lia.
Qed.

Lemma open_ro_shu : forall Σ OW LB m ls PL EA SPX r a,
  AHEAP Σ OW LB m -> lib_state ls m OW PL EA -> frames_ok PL SPX USTACK_TOP -> pl_frames PL = [] -> ref_at ls OW PL r a -> not_one r ->
  exists D, rw_cells bgbsegs m a (bn_cells D (getbn r ls)) /\ bg_ok (getbn r ls)
    /\ u64arr bgbsegs m D (wlimbs (bn_buf (getbn r ls)))
    /\ 0 < a /\ a + 24 <= ACEIL /\ 0 <= D /\ D + 8 * Z.of_nat (bn_dmax (getbn r ls)) <= ACEIL
    /\ acc bgbsegs m a 24 /\ a mod 8 = 0
    /\ acc bgbsegs m D (8 * Z.of_nat (bn_top (getbn r ls))) /\ D mod 8 = 0
    /\ ub_ptr_ok (Z.of_nat (bn_top (getbn r ls))) D /\ ub_ptr_ok (Z.of_nat (bn_dmax (getbn r ls))) D.
Proof.
  intros Σ OW LB m ls PL EA SPX r a HEAP LS FROK NOFR HA NRO.
  destruct (open_full Σ OW LB m ls PL EA SPX r a HEAP LS FROK NOFR HA NRO) as (D & SA & ARR & OK & U & A0 & AC & D0 & DC & _).
  destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAP LS NOFR HA NRO) as (ACS & ALS & _).
  destruct (arr_shA _ _ _ _ _ _ HEAP ARR) as (ACD & ALD & _).
  pose proof OK as (_ & TD & _).
  exists D. do 7 (split; [assumption|]). split; [exact ACS|]. split; [exact ALS|].
  split; [eapply acc_sub; [exact ACD | lia | unfold bn_dmax in *; lia]|]. split; [exact ALD|].
  split; [apply (arr_ub_okA Σ OW LB m D (getbn r ls) _ HEAP ARR); unfold bn_dmax in *; lia | apply (arr_ub_okA Σ OW LB m D (getbn r ls) _ HEAP ARR); lia].
Qed.

End WithRT.
