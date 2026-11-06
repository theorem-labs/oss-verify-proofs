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
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Malloc Prog BnBase BnModel BnTree BnInv BnSpecs BnMInv BgState BgInv BgLib.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgB Require Import Layout R_unwind_chain RT_iface RT_client_kit D_defs I_lkit.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnMem.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import AsKit AsLoop.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require Import LibKitA ARun BnHeapA ImplA ImplAX UnwindA.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require BnRepDefs BnRepA BnIfaceA.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepB Require Import BgRepDefs BgRep BgLayer BgIface.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require Import BnAKitAF BnCallAF AFrameKit AFrameEnv.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepB Require Import BgLayerF BgIfaceF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma ref_at_montRR : forall (st : bstate bptr) OW PL am qm, pl_mont PL = Some (am, qm) -> ref_at st OW PL RMontRR am.
Proof.
  intros st OW PL am qm E. apply ref_at_fixed; [unfold RMontRR, NFIX; lia|]. exists (PHeap am qm 0).
  unfold pl_of. rewrite E. cbn. split; reflexivity.
Qed.
Lemma ref_at_montN : forall (st : bstate bptr) OW PL am qm, pl_mont PL = Some (am, qm) -> ref_at st OW PL RMontN (am + 24).
Proof.
  intros st OW PL am qm E. apply ref_at_fixed; [unfold RMontN, NFIX; lia|]. exists (PHeap (am + 24) qm 24).
  unfold pl_of. rewrite E. cbn. split; reflexivity.
Qed.
Lemma RMontRR_not_one : RMontRR <> ROne. Proof. unfold RMontRR, ROne; lia. Qed.
Lemma RMontN_not_one : RMontN <> ROne. Proof. unfold RMontN, ROne; lia. Qed.

Definition pl_fresh (PL : placement) : Prop :=
  pl_bn PL RRecpN = None /\ pl_bn PL RRecpNr = None /\ pl_recp PL = None /\ pl_mont PL = None /\ pl_bn PL RTmod = None.

Section Stmt.
Context {AR : ARun} {UK : UnwindKit}.
Local Notation RT := (@ar_RT AR).

Definition exp_stmtA (ENTRY STACK COST : Z) (depth : nat) (one : bnref -> bnref -> bnref -> bnref -> BM (M:=btree bptr) (ptr:=bptr) unit)
    (sixth : option word) : Prop := forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
    (lo : Z) (ras : list Z) (rr ra_ rp rm : bnref) (arr ara arp arm ac : Z) (qc : bptr),
  bn_preA Σ ls m OW LB PL EA sp lo STACK COST -> fr_room depth ls OW LB ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx ENTRY (bv_unsigned ra :: ras) ->
  tp = wz TP_A ->
  ref_at ls OW PL rr arr -> ref_at ls OW PL ra_ ara -> ref_at ls OW PL rp arp -> ref_at ls OW PL rm arm ->
  hpl PL rr -> ra_ <> ROne -> rp <> ROne -> rm <> ROne -> pl_ctx PL = Some (ac, qc) ->
  a0 = wz arr -> a1 = wz ara -> a2 = wz arp -> a3 = wz arm -> a4 = wz ac -> (forall w, sixth = Some w -> a5 = w) ->
  implA (one rr ra_ rp rm ls) Σ
    (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA COST (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz ENTRY) fc None m (seg_rom bgbsegs)).

Definition exp_stmtA_f (ENTRY STACK COST : Z) (depth : nat) (one : bnref -> bnref -> bnref -> bnref -> BM (M:=btree bptr) (ptr:=bptr) unit)
    (sixth : option word) : Prop := forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
    (lo : Z) (ras : list Z) (rr ra_ rp rm : bnref) (arr ara arp arm ac : Z) (qc : bptr),
  bn_preA Σ ls m OW LB PL EA sp lo STACK COST -> fr_room depth ls OW LB ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx ENTRY (bv_unsigned ra :: ras) ->
  tp = wz TP_A ->
  ref_at ls OW PL rr arr -> ref_at ls OW PL ra_ ara -> ref_at ls OW PL rp arp -> ref_at ls OW PL rm arm ->
  hpl PL rr -> ra_ <> ROne -> rp <> ROne -> rm <> ROne -> pl_ctx PL = Some (ac, qc) -> pl_fresh PL ->
  a0 = wz arr -> a1 = wz ara -> a2 = wz arp -> a3 = wz arm -> a4 = wz ac -> (forall w, sixth = Some w -> a5 = w) ->
  implA (one rr ra_ rp rm ls) Σ
    (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA COST (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz ENTRY) fc None m (seg_rom bgbsegs)).
End Stmt.

Section WithRT.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Lemma MC0 : 0 <= MC. Proof. unfold MC. lia. Qed.

Lemma const_one_acc : forall Σ OW LB m, AHEAP Σ OW LB m -> acc bgbsegs m CONST_ONE 24.
Proof.
  intros Σ OW LB m H.
  apply (af_lib_acc_lit RT AF Σ m (CONST_ONE, 24, 64) CONST_ONE 24 (AH_art _ _ _ _ H)); [vm_compute; reflexivity | cbn; lia | cbn; lia].
Qed.

Lemma top_small : forall (st : bstate bptr) m OW PL EA r a, lib_state st m OW PL EA -> ref_at st OW PL r a -> Z.of_nat (bn_top (getbn r st)) <= 512.
Proof.
  intros st m OW PL EA r a LS HA. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HA) as HV.
  pose proof (proj1 (lib_state_h_parts _ _ _ _ _ _ LS)) as WF.
  destruct (Nat.eq_dec r ROne) as [->|NE].
  - destruct WF as (_ & _ & W3 & _). rewrite W3. cbn. lia.
  - pose proof (st_wf_ok r st WF HV NE) as (_ & T & D & _). unfold BG_DMAX in D. lia.
Qed.

Lemma ref_sh_any : forall Σ OW LB m (ls : bstate bptr) PL EA SPX r a,
  AHEAP Σ OW LB m -> lib_state ls m OW PL EA -> frames_ok LB PL SPX USTACK_TOP -> frames_lb PL LB -> ref_at ls OW PL r a ->
  acc bgbsegs m a 24 /\ a mod 8 = 0 /\ 0 < a /\ a + 24 <= ACEIL.
Proof.
  intros Σ OW LB m ls PL EA SPX r a HEAP LS FROK NOFR HA.
  destruct (Nat.eq_dec r ROne) as [->|NE].
  - pose proof (ref_at_fun _ _ _ _ _ _ (AH_nodup_l _ _ _ _ HEAP) HA (ref_at_one ls OW PL)) as ->.
    pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & _). unfold SEGTOP_A in C1.
    split; [exact (const_one_acc _ _ _ _ HEAP)|]. unfold CONST_ONE. split; [reflexivity|]. split; [lia|]. unfold BnHeapA.ACEIL in *. lia.
  - destruct (open_ro_sh Σ OW LB m ls PL EA SPX r a HEAP LS FROK NOFR HA NE) as (D & _ & _ & _ & A0 & AC & _ & _ & ACC & AL & _).
    split; [exact ACC|]. split; [exact AL|]. split; [exact A0| exact AC].
Qed.

Lemma implA_post_evt : forall {A} (t : btree bptr A) Σ (Q1 Q : A -> rts RT -> machine_state -> Prop) ms,
  implA t Σ Q1 ms -> (forall a Σ' ms', Q1 a Σ' ms' -> evt bgbsegs (Q a Σ') ms') -> implA t Σ Q ms.
Proof.
  intros A t Σ Q1 Q ms H HK X Φ S T c Hc Hk.
  apply (H X Φ S T c Hc).
  intros c' (a & X' & Σ' & HΦ & Hc').
  apply (asta_evtA Σ' (Q1 a Σ') (Q a Σ') (HK a Σ') T c' Hc').
  intros c'' Hc''. apply Hk. exists a, X', Σ'. split; [exact HΦ | exact Hc''].
Qed.

Lemma bn_preA_wk : forall Σ (st : bstate bptr) m OW LB PL EA sp lo K K' C C',
  bn_preA Σ st m OW LB PL EA sp lo K C -> K' <= K -> C' <= C -> bn_preA Σ st m OW LB PL EA sp lo K' C'.
Proof.
  intros Σ st m OW LB PL EA sp lo K K' C C' (HEAP & LS & FROK & ST & CEIL & LO & SPT & SP16 & MI & CNT & CRED & FAL & NOFR) HK HC.
  unfold bn_preA.
  split; [exact HEAP|]. split; [exact LS|]. split; [exact FROK|]. split; [exact ST|]. split; [exact CEIL|]. split; [clear - LO HK; lia|].
  split; [exact SPT|]. split; [exact SP16|]. split; [exact MI|]. split; [exact CNT|]. split; [clear - CRED HC; lia|]. split; [exact FAL| exact NOFR].
Qed.

Lemma bn_postA_wk : forall {A : Type} (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    Σ (st : bstate bptr) OW LB lo m PL EA C C' (RES : A -> bstate bptr -> list block -> placement -> word -> Prop) r Σ' ms',
  bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ st OW LB lo m PL EA C RES r Σ' ms' -> C <= C' ->
  bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ st OW LB lo m PL EA C' RES r Σ' ms'.
Proof.
  intros A ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ st OW LB lo m PL EA C C' RES r Σ' ms' PO HC. unfold bn_postA in *.
  destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & F2 & fc2 & m2 & OW2 & PL2 & E & HEAP2 & LS2 & ST2 & MI2 & AXP2 & CRED2 & CNT2 & RST2 & RES2).
  exists y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, F2, fc2, m2, OW2, PL2.
  split; [exact E|]. split; [exact HEAP2|]. split; [exact LS2|]. split; [exact ST2|]. split; [exact MI2|]. split; [exact AXP2|].
  split; [clear - CRED2 HC; lia|]. split; [exact CNT2|]. split; [exact RST2| exact RES2].
Qed.

Lemma implA_cost_wk : forall {A : Type} (t : btree bptr (A * bstate bptr)) (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    Σ (st : bstate bptr) OW LB lo m PL EA C C' (RES : A -> bstate bptr -> list block -> placement -> word -> Prop) ms,
  implA t Σ (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ st OW LB lo m PL EA C RES) ms -> C <= C' ->
  implA t Σ (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ st OW LB lo m PL EA C' RES) ms.
Proof.
  intros A t ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ st OW LB lo m PL EA C C' RES ms H HC.
  eapply implA_mono; [exact H|]. intros a Σ' ms' PO. eapply bn_postA_wk; [exact PO| exact HC].
Qed.

Section Env.
  Variables (LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs) (lo SPv FB : Z) (s0w raw : word) (rasO : option (list Z)) (TOTAL : Z).
  Variables (Σ0 : rts RT) (ls0 : bstate bptr) (OW0 : list block) (m0 : mem).
  Notation CENV := (cenvA LB PL lo SPv FB s0w raw rasO TOTAL Σ0 ls0 OW0 m0).

  Lemma cenv_roomA : forall pre used Σ (ls : bstate bptr) m OW d d',
    CENV pre used Σ ls m OW -> fr_room d ls0 OW0 LB -> (d' <= d)%nat -> fr_room d' ls OW LB.
  Proof.
    intros pre used Σ ls m OW d d' (OK & HEAP & ST & MI & AXP & CR & CNT & _) R L.
    exact (fr_room_callee d d' ls0 OW0 ls OW LB R CNT L).
  Qed.

  Lemma cenv_tailA : forall pre used Σ (ls : bstate bptr) m OW K C ras
      (ra gp x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : word) {A : Type}
      (RES : A -> bstate bptr -> list block -> placement -> word -> Prop),
    CENV pre used Σ ls m OW -> lib_state ls m OW PL EA -> stk bgbsegs m lo SPv -> lo <= SPv - K -> used + C <= TOTAL -> rasO = Some ras ->
    bn_preA Σ ls m OW LB PL EA (Z_to_bv 64 SPv) lo K C
    /\ uw_chain USTACK_TOP m SPv (bv_unsigned s0w) ras
    /\ (forall r Σ' ms', bn_postA ra (Z_to_bv 64 SPv) gp x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 Σ ls OW LB lo m PL EA C RES r Σ' ms' ->
                         bn_postA ra (Z_to_bv 64 SPv) gp x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 Σ0 ls0 OW0 LB lo m0 PL EA TOTAL RES r Σ' ms').
  Proof.
    intros until RES. intros ENV LS ST' LOK HC ER.
    pose proof ENV as (OK & HEAP & ST & MI & AXP & CR & CNT & RS & FR & FSZ & UW).
    pose proof OK as (CEIL & LOFB & FBSP & SPT & SP16 & FB16 & CNT0 & CRED0 & FROK & FAL & NOFR).
    assert (ESP : bv_unsigned (Z_to_bv 64 SPv) = SPv).
    { pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & _). unfold SEGTOP_A, USTACK_TOP in *. apply unsigned_lit. clear - C1 CEIL LOFB FBSP SPT. lia. }
    split; [|split].
    - unfold bn_preA. rewrite ESP.
      split; [exact HEAP|]. split; [exact LS|]. split; [exact FROK|]. split; [exact ST'|]. split; [exact CEIL|]. split; [exact LOK|].
      split; [exact SPT|]. split; [exact SP16|]. split; [exact MI|]. split; [exact (cnt_ok_eq _ _ _ _ _ CNT0 CNT)|]. split; [clear - CR CRED0 HC; lia|].
      split; [exact FAL| exact NOFR].
    - unfold uw_opt in UW. rewrite ER in UW. exact UW.
    - intros r Σ' ms' PO. unfold bn_postA in *. rewrite ESP in *.
      destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & F2 & fc2 & m2 & OW2 & PL2 & E & HEAP2 & LS2 & ST2 & MI2 & AXP2 & CRED2 & CNT2 & RST2 & RES2).
      exists y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, F2, fc2, m2, OW2, PL2.
      split; [exact E|]. split; [exact HEAP2|]. split; [exact LS2|]. split; [exact ST2|]. split; [exact MI2|].
      split; [eapply ax_pres_trans; [exact AXP| exact AXP2]|].
      split; [clear - CR CRED2 HC; lia|].
      split; [eapply cnt_eq_trans; [exact CNT| exact CNT2]|].
      split; [eapply refs_stable_trans; [exact RS| exact RST2]| exact RES2].
  Qed.
End Env.

End WithRT.
