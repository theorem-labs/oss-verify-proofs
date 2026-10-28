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
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnModel BnTree BnInv BnBridge BgState BgInv BgLib BgArith BgMont.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Import Layout Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnMem BnTac BnTacX.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnArr.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require Import BnHeap W_small W_top.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require BnRep.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgRepU Require Import BgRepDefs BgRep BgLayer BgIface BnUAlign.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnBoth Require Import UbKit.
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

Definition BN_MUL_MONT_FIXED_TOP : Z := 0xffeec.
Definition BN_MOD_MUL_MONTGOMERY : Z := 0xffea4.
Definition BN_TO_MONT_FIXED_TOP : Z := 0x1003b4.
Definition BN_TO_MONTGOMERY : Z := 0xffbd0.
Definition BN_FROM_MONT_FIXED_TOP : Z := 0x100310.
Definition BN_FROM_MONTGOMERY : Z := 0x1002c8.

Definition BN_FROM_MONTGOMERY_WORD : Z := 0x100010.
Definition BN_SQR_FIXED_TOP : Z := 0x1073bc.
Definition BN_MUL_FIXED_TOP : Z := 0x1026d8.
Definition BN_CTX_START : Z := 0x100c14.
Definition BN_CTX_GET : Z := 0x100e84.
Definition BN_CTX_END : Z := 0x100da4.
Definition BN_COPY : Z := 0xfe304.

Lemma ref_at_range_any : forall st OW PL EA SPX BX s LB m r a,
  RHEAP s (OW ++ LB) m -> lib_parts st OW PL EA -> frames_ok PL SPX BX -> ref_at st OW PL r a ->
  0 < a /\ (a + 24 <= alloc_ceiling \/ (SPX <= a /\ a + 24 < 2^63)).
Proof.
  intros st OW PL EA SPX BX s LB m r a HEAP PARTS FROK HA.
  destruct (Nat.eq_dec r ROne) as [->|NE].
  - pose proof (ref_at_fun _ _ _ _ _ _ (RH_nodup_l _ _ _ _ HEAP) HA (ref_at_one st OW PL)) as ->.
    unfold CONST_ONE. split; [lia| left; lia].
  - pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK HA NE) as (X & Y & _). split; [exact X| exact Y].
Qed.

Lemma top_small : forall st m OW PL EA r a, lib_state st m OW PL EA -> ref_at st OW PL r a -> Z.of_nat (bn_top (getbn r st)) <= 512.
Proof.
  intros st m OW PL EA r a LS HA. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HA) as HV.
  pose proof (proj1 (lib_state_h_parts _ _ _ _ _ _ LS)) as WF.
  destruct (Nat.eq_dec r ROne) as [->|NE].
  - rewrite (proj1 (proj2 (proj2 (proj2 (proj2 WF))))) || (destruct WF as (W1 & W2 & W3 & W4); rewrite W3 || rewrite W4). cbn. lia.
  - pose proof (st_wf_ok r st WF HV NE) as (_ & T & D & _). unfold BG_DMAX in D. lia.
Qed.

Lemma ref_at_montRR : forall st OW PL am qm, pl_mont PL = Some (am, qm) -> ref_at st OW PL RMontRR am.
Proof.
  intros st OW PL am qm E. apply ref_at_fixed; [unfold RMontRR, NFIX; lia|]. exists (PHeap am qm 0).
  unfold pl_of. rewrite E. cbn. split; reflexivity.
Qed.
Lemma ref_at_montN : forall st OW PL am qm, pl_mont PL = Some (am, qm) -> ref_at st OW PL RMontN (am + 24).
Proof.
  intros st OW PL am qm E. apply ref_at_fixed; [unfold RMontN, NFIX; lia|]. exists (PHeap (am + 24) qm 24).
  unfold pl_of. rewrite E. cbn. split; reflexivity.
Qed.
Lemma wref_montRR : forall PL am qm, pl_mont PL = Some (am, qm) -> wref PL RMontRR.
Proof. intros PL am qm E. eapply wref_heap. unfold pl_of. rewrite E. cbn. reflexivity. Qed.
Lemma RMontRR_not_one : RMontRR <> ROne. Proof. unfold RMontRR, ROne; lia. Qed.
Lemma RMontN_not_one : RMontN <> ROne. Proof. unfold RMontN, ROne; lia. Qed.

Lemma ref_at_ualign_any : forall st OW PL EA s LB m r a,
  RHEAP s (OW ++ LB) m -> lib_parts st OW PL EA -> ref_at st OW PL r a -> 0 < a /\ a mod 8 = 0.
Proof.
  intros st OW PL EA s LB m r a HEAP PARTS HA.
  destruct (Nat.eq_dec r ROne) as [->|NE].
  - pose proof (ref_at_fun _ _ _ _ _ _ (RH_nodup_l _ _ _ _ HEAP) HA (ref_at_one st OW PL)) as ->.
    unfold CONST_ONE. split; [lia| reflexivity].
  - exact (ref_at_ualign _ _ _ _ _ _ _ _ _ HEAP PARTS HA NE).
Qed.

Ltac hide_ors := repeat match goal with H : _ \/ _ |- _ => apply hide_intro in H end.
Ltac unhide := repeat match goal with H : hide _ |- _ => apply hide_elim in H end.
Ltac sp16 :=
  lazymatch goal with H : bv_unsigned ?s mod 16 = 0 |- _ =>
    first [ exact H
          | (rewrite ?unsigned_lit by lia; clear - H; Z.div_mod_to_equations; lia)
          | (rewrite ?unsigned_lit by lia; Z.div_mod_to_equations; lia) ] end.

Section Proofs.

  Variable CS : Z.
  Hypothesis CS16 : 16 <= CS.
  Definition MONT_MUL_STACK : Z := 64 + CS.
  Definition MONT_MUL2_STACK : Z := 96 + CS.

  Local Notation REGS P := (forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word), P ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s bs OW LB PL EA lo B errv) (only parsing).

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

  Hypothesis BN_copy_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (rx ry : bnref) (ax ay : Z),
    bn_pre s bs m OW LB PL EA sp lo B errv CS -> tp = wz RATP ->
    ref_at bs OW PL rx ax -> ref_at bs OW PL ry ay -> wref PL rx -> ry <> ROne -> a0 = wz ax -> a1 = wz ay ->
    implM bgusegs (interp (embed (BN_copy (tree_ops bptr) rx ry bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA
               (fun _ _ OW' PL' a0' => PL' = PL /\ a0' = wz ax /\ (forall q A n, In (q, A, n) OW -> bn_d (getbn rx bs) <> Some q -> In (q, A, n) OW')))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_COPY) fc None m (seg_rom bgusegs)).

  Hypothesis bn_sqr_fixed_top_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (rr rx : bnref) (ar ax ac : Z) (qc : bptr),
    bn_pre s bs m OW LB PL EA sp lo B errv CS -> tp = wz RATP -> bv_unsigned sp mod 16 = 0 ->
    ref_at bs OW PL rr ar -> ref_at bs OW PL rx ax -> hpl PL rr -> rx <> ROne -> pl_ctx PL = Some (ac, qc) ->
    a0 = wz ar -> a1 = wz ax -> a2 = wz ac ->
    implM bgusegs (interp (embed (bn_sqr_fixed_top (tree_ops bptr) rr rx bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_SQR_FIXED_TOP) fc None m (seg_rom bgusegs)).

  Hypothesis bn_mul_fixed_top_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (rr rx ry : bnref) (ar ax ay ac : Z) (qc : bptr),
    bn_pre s bs m OW LB PL EA sp lo B errv CS -> tp = wz RATP ->
    ref_at bs OW PL rr ar -> ref_at bs OW PL rx ax -> ref_at bs OW PL ry ay -> hpl PL rr -> ry <> ROne -> pl_ctx PL = Some (ac, qc) ->
    a0 = wz ar -> a1 = wz ax -> a2 = wz ay -> a3 = wz ac ->
    implM bgusegs (interp (embed (bn_mul_fixed_top (tree_ops bptr) rr rx ry bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_MUL_FIXED_TOP) fc None m (seg_rom bgusegs)).

  Hypothesis bn_from_montgomery_word_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (rt rx : bnref) (at_ ax am : Z) (qm : bptr),
    bn_pre s bs m OW LB PL EA sp lo B errv CS -> tp = wz RATP ->
    ref_at bs OW PL rt at_ -> ref_at bs OW PL rx ax -> wref PL rt -> wref PL rx -> pl_mont PL = Some (am, qm) ->
    a0 = wz at_ -> a1 = wz ax -> a2 = wz am ->
    implM bgusegs (interp (embed (bn_from_montgomery_word (tree_ops bptr) rt rx bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_FROM_MONTGOMERY_WORD) fc None m (seg_rom bgusegs)).

  Definition mont3_stmt (ENTRY STACK : Z) (f : bnref -> bnref -> bnref -> BM unit) : Prop := forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (rr ra_ rb : bnref) (ar aa ab am ac : Z) (qm qc : bptr),
    bn_pre s bs m OW LB PL EA sp lo B errv STACK -> tp = wz RATP -> bv_unsigned sp mod 16 = 0 ->
    ref_at bs OW PL rr ar -> ref_at bs OW PL ra_ aa -> ref_at bs OW PL rb ab -> wref PL rr -> rb <> ROne ->
    pl_mont PL = Some (am, qm) -> pl_ctx PL = Some (ac, qc) ->
    a0 = wz ar -> a1 = wz aa -> a2 = wz ab -> a3 = wz am -> a4 = wz ac ->
    implM bgusegs (interp (embed (f rr ra_ rb bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz ENTRY) fc None m (seg_rom bgusegs)).

  Definition mont2_stmt (ENTRY STACK : Z) (f : bnref -> bnref -> BM unit) (nro : bool) : Prop := forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (rr ra_ : bnref) (ar aa am ac : Z) (qm qc : bptr),
    bn_pre s bs m OW LB PL EA sp lo B errv STACK -> tp = wz RATP -> bv_unsigned sp mod 16 = 0 ->
    ref_at bs OW PL rr ar -> ref_at bs OW PL ra_ aa -> wref PL rr -> (nro = true -> ra_ <> ROne) ->
    pl_mont PL = Some (am, qm) -> pl_ctx PL = Some (ac, qc) ->
    a0 = wz ar -> a1 = wz aa -> a2 = wz am -> a3 = wz ac ->
    implM bgusegs (interp (embed (f rr ra_ bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz ENTRY) fc None m (seg_rom bgusegs)).

  Lemma bn_mul_mont_fixed_top_walk : mont3_stmt BN_MUL_MONT_FIXED_TOP MONT_MUL_STACK (bn_mul_mont_fixed_top (tree_ops bptr)).
  Proof.
    unfold mont3_stmt. intros until qc. intros (HEAP & LS & FROK & AUX & SPB & B63 & ST & CEIL & GLO & LO & ERR & MI) -> SP16 HAr HAa HAb WRr NROb HPM HPC -> -> -> -> ->.
    unfold MONT_MUL_STACK, BN_MUL_MONT_FIXED_TOP, GLOBALS_TOP, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
    pose proof (ref_at_montN bs OW PL am qm HPM) as HAn.

    assert (AaR : 0 < aa < 2^64) by (pose proof (ref_at_range_any _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK HAa) as (X & Y); clear - X Y SPR; lia).
    assert (AbR : 0 < ab < 2^64) by (pose proof (ref_at_range_any _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK HAb) as (X & Y); clear - X Y SPR; lia).
    assert (SEPa : aa + 24 <= bv_unsigned sp - 64 \/ bv_unsigned sp <= aa) by (pose proof (ref_at_range_any _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK HAa) as (X & Y); clear - X Y CEIL LO CS16; lia).
    assert (SEPb : ab + 24 <= bv_unsigned sp - 64 \/ bv_unsigned sp <= ab) by (pose proof (ref_at_range_any _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK HAb) as (X & Y); clear - X Y CEIL LO CS16; lia).
    assert (SEPn : am + 24 + 24 <= bv_unsigned sp - 64 \/ bv_unsigned sp <= am + 24) by (pose proof (ref_at_range_any _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK HAn) as (X & Y); clear - X Y CEIL LO CS16; lia).
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgusegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3346328 - 164) with 3346164 in ERR.
    assert (GLO' : GLOBALS_TOP <= lo) by exact GLO.

    unfold bn_mul_mont_fixed_top, bbind, bget, bret, bunr. cbn [bind ret unreachable tree_ops tbind fst snd].
    set (bn := getbn RMontN bs). set (ba := getbn ra_ bs). set (bb := getbn rb bs).
    pose proof (top_small _ _ _ _ _ _ _ LS HAn) as Tn. pose proof (top_small _ _ _ _ _ _ _ LS HAa) as Ta. pose proof (top_small _ _ _ _ _ _ _ LS HAb) as Tb.
    fold bn in Tn. fold ba in Ta. fold bb in Tb.
    unfold implM. iprefix.

    carve_frame 64%nat ST. do 10 step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HWL : Forall (w_lib bs OW PL lo (bv_unsigned sp)) [(bv_unsigned sp + -64, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
    assert (WOK : Forall (w_ok OW LB bs PL EA (bv_unsigned sp) []) [(bv_unsigned sp + -64, bv_unsigned sp)]) by (constructor; [apply w_stack; cbn; lia| constructor]).
    pose proof (lib_state_frame s LB _ _ [] bs m m1 OW PL EA _ HEAP LS MU WM FROK WOK) as LS1.

    destruct (lib_state_open_ro [] bs m1 OW PL EA ra_ aa LS1 ND HAa ltac:(intros [])) as ((Da & BNa & _) & _ & _ & _).
    destruct (lib_state_open_ro [] bs m1 OW PL EA rb ab LS1 ND HAb ltac:(intros [])) as ((Db & BNb & _) & _ & _ & _).
    destruct (lib_state_open_ro [] bs m1 OW PL EA RMontN (am + 24) LS1 ND HAn ltac:(intros [])) as ((Dn & BNn & _) & _ & _ & _).
    fold ba in BNa. fold bb in BNb. fold bn in BNn. unfold bn_cells in BNa, BNb, BNn.
    destruct (ref_at_ualign_any _ _ _ _ _ _ _ _ _ HEAP PARTS (ref_at_montRR bs OW PL am qm HPM)) as (AM0 & AM8).
    destruct (ref_at_ualign_any _ _ _ _ _ _ _ _ _ HEAP PARTS HAa) as (AA0 & AA8).
    destruct (ref_at_ualign_any _ _ _ _ _ _ _ _ _ HEAP PARTS HAb) as (AB0 & AB8).
    assert (AMR : am < 2^64) by (pose proof (ref_at_range_any _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK HAn) as (X & Y); clear - X Y; lia).

    hide_ors.
    ub_chk. step. step. zstep. ub_chk.
    step. ub_chk. zstep. ub_chk.
    step. ub_chk. zstep. ub_chk.
    unhide.
    step. unfold MallocRep.wz at 1. rewrite (sx32_small (Z.of_nat (bn_top ba))) by (clear - Ta; lia).
    step. unfold MallocRep.wz at 1. rewrite (sx32_small (Z.of_nat (bn_top bb))) by (clear - Tb; lia).
    step. rewrite !unsigned_lit by (clear - Ta Tb; lia). rewrite (bn_swrap32_small _) by (clear - Ta Tb; lia).
    zstep. hide_ors. ub_chk. unhide.
    step. unfold MallocRep.wz at 1. rewrite (sx32_small (Z.of_nat (bn_top bn))) by (clear - Tn; lia).
    zstep. step. rewrite ?unsigned_lit by (clear - Tn; lia). rewrite (bn_swrap32_small _) by (clear - Tn; lia).
    hide_ors. ub_chk. unhide.
    step. rewrite unsigned_lit by (clear - Tn; lia). rewrite Z.shiftl_mul_pow2, Z.pow_1_r by lia. rewrite (bn_swrap32_small _) by (clear - Tn; lia).
    step. rewrite lts_small by (clear - Ta Tb Tn; lia).
    destruct (Z.ltb_spec (Z.of_nat (bn_top bn) * 2) (Z.of_nat (bn_top ba) + Z.of_nat (bn_top bb))) as [LT|GE]; cbn [negb].
    { replace (2 * bn_top bn <? bn_top ba + bn_top bb)%nat with true by (symmetry; apply Nat.ltb_lt; clear - LT; lia).
      ihere. to_implM. cbn [embed interp]. apply implM_interp_unr. }
    replace (2 * bn_top bn <? bn_top ba + bn_top bb)%nat with false by (symmetry; apply Nat.ltb_ge; clear - GE; lia).
    clear BNa BNb BNn Da Db Dn.
    step. step. step.

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
    replace (ret_pc (Z_to_bv 64 1048456)) with (Z_to_bv 64 1048456) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

    unfold implM. iprefix. step. step.
    destruct (KPRE _ _ _ _ _ CS ENV2 LS2 LOF) as (errv2 & PRE2).
    ihere. to_implM.
    eapply implM_embed_bind.
    { eapply BN_CTX_get_walk; [exact PRE2| reflexivity| exact HPC| reflexivity]. }
    cbv beta. intros [t bs2] st2 ms2 PO. apply BPK in PO; [|intros v b o p a [E _]; exact E].
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m3 & OW3 & -> & KP & (_ & (ti & Et) & (at_ & HAt & ->) & INCL3)).
    destruct (KPOST _ _ _ _ _ _ _ _ _ ENV2 KP) as (ENV3 & LS3). pose proof KP as RS3; apply kpost_refs in RS3.
    cbn [fst snd] in *. clear PRE2 KP ENV2 LS2.
    replace (ret_pc (Z_to_bv 64 1048464)) with (Z_to_bv 64 1048464) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

    pose proof (refs_stable_trans _ _ _ _ _ _ RS2 RS3) as RS13.
    pose proof (ref_at_stable _ _ _ _ PL _ _ RS13 HAr) as HAr3. pose proof (ref_at_stable _ _ _ _ PL _ _ RS13 HAa) as HAa3.
    pose proof (ref_at_stable _ _ _ _ PL _ _ RS13 HAb) as HAb3.
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
        pose proof (struct_disj st2 OW3 LB m3 HEAP3 bs2 PL EA _ _ PARTS3 FROK3 ra_ rb aa ab NE HAa3 HAb3) as D. clear - D KE. lia. }
      subst rb. rewrite Nat.eqb_refl.
      step. step.
      destruct (KPRE _ _ _ _ _ CS ENV3 LS3 LOF) as (errv3 & PRE3).
      ihere. to_implM.
      eapply implM_embed_bind.
      { eapply bn_sqr_fixed_top_walk; [exact PRE3| reflexivity| sp16| exact HAt| exact HAa3| rewrite Et; apply hpl_pool| exact NROb| exact HPC| reflexivity| reflexivity| reflexivity]. }
      cbv beta. intros [u4 bs4] st4 ms4 PO. apply BPK in PO; [|intros v b o p a [E _]; exact E].
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m4 & OW4 & -> & KP & (_ & ->)).
      destruct (KPOST _ _ _ _ _ _ _ _ _ ENV3 KP) as (ENV4 & LS4). pose proof KP as RS4; apply kpost_refs in RS4.
      cbn [fst snd] in *. clear PRE3 KP.
      replace (ret_pc (Z_to_bv 64 1048528)) with (Z_to_bv 64 1048528) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      unfold implM. iprefix. step. if_true.

      step. step. step. step.
      destruct (KPRE _ _ _ _ _ CS ENV4 LS4 LOF) as (errv4 & PRE4).
      pose proof (refs_stable_trans _ _ _ _ _ _ RS13 RS4) as RS14.
      ihere. to_implM.
      eapply implM_embed_bind.
      { eapply bn_from_montgomery_word_walk; [exact PRE4| reflexivity| exact (ref_at_stable _ _ _ _ PL _ _ RS14 HAr)| exact (ref_at_stable _ _ _ _ PL _ _ RS4 HAt)
          | exact WRr| rewrite Et; apply wref_pool| exact HPM| reflexivity| reflexivity| reflexivity]. }
      cbv beta. intros [u5 bs5] st5 ms5 PO. apply BPK in PO; [|intros v b o p a [E _]; exact E].
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m5 & OW5 & -> & KP & (_ & ->)).
      destruct (KPOST _ _ _ _ _ _ _ _ _ ENV4 KP) as (ENV5 & LS5). pose proof KP as RS5; apply kpost_refs in RS5.
      cbn [fst snd] in *. clear PRE4 KP.
      replace (ret_pc (Z_to_bv 64 1048512)) with (Z_to_bv 64 1048512) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

      unfold implM. iprefix. step. step. step. step.
      destruct (KPRE _ _ _ _ _ CS ENV5 LS5 LOF) as (errv5 & PRE5).
      ihere. to_implM.
      eapply implM_post_evt.
      { eapply BN_CTX_end_walk; [exact PRE5| reflexivity| exact HPC| reflexivity]. }
      cbv beta. intros [u6 bs6] st6 ms6 PO. apply BPK in PO; [|intros v b o p a [E _]; exact E].
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m6 & OW6 & -> & KP & (_ & EOW6)).
      destruct (KPOST _ _ _ _ _ _ _ _ _ ENV5 KP) as (ENV6 & LS6). pose proof KP as RS6; apply kpost_refs in RS6.
      cbn [fst snd] in *. clear PRE5 KP.
      replace (ret_pc (Z_to_bv 64 1048544)) with (Z_to_bv 64 1048544) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof (kenv_final LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -64) s bs OW m _ _ _ _ _ ENV6) as (F1 & F2 & STF & (errvF & F4) & F5 & F6 & F7 & F8 & F9 & FRF).

      step. do 8 step. release_frame FRF STF (bv_unsigned sp). step. step.
      apply evt_done. unfold bn_post. do 15 eexists. exists m6, OW6, PL, errvF. split; [reflexivity|]. cbn [fst snd].
      split; [exact F1|]. split; [exact LS6|]. split; [exact F2|]. split; [exact STF|]. split; [exact F4|]. split; [exact F5|].
      split; [exact F6|]. split; [exact F7|]. split; [exact F8|]. split; [first [eapply refs_stable_trans; [exact F9| exact RS6] | exact F9]|]. split; reflexivity.
    -
      assert (NE : ra_ <> rb).
      { intros E. subst rb. pose proof (ref_at_fun _ _ _ _ _ _ ND3 HAa3 HAb3) as EA_. clear - EA_ KE. lia. }
      replace ((ra_ =? rb)%nat) with false by (symmetry; apply Nat.eqb_neq; exact NE).
      step. step. step.
      destruct (KPRE _ _ _ _ _ CS ENV3 LS3 LOF) as (errv3 & PRE3).
      ihere. to_implM.
      eapply implM_embed_bind.
      { eapply bn_mul_fixed_top_walk; [exact PRE3| reflexivity| exact HAt| exact HAa3| exact HAb3| rewrite Et; apply hpl_pool| exact NROb| exact HPC
          | reflexivity| reflexivity| reflexivity| reflexivity]. }
      cbv beta. intros [u4 bs4] st4 ms4 PO. apply BPK in PO; [|intros v b o p a [E _]; exact E].
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m4 & OW4 & -> & KP & (_ & ->)).
      destruct (KPOST _ _ _ _ _ _ _ _ _ ENV3 KP) as (ENV4 & LS4). pose proof KP as RS4; apply kpost_refs in RS4.
      cbn [fst snd] in *. clear PRE3 KP.
      replace (ret_pc (Z_to_bv 64 1048492)) with (Z_to_bv 64 1048492) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      unfold implM. iprefix. step. if_false.

      step. step. step. step.
      destruct (KPRE _ _ _ _ _ CS ENV4 LS4 LOF) as (errv4 & PRE4).
      pose proof (refs_stable_trans _ _ _ _ _ _ RS13 RS4) as RS14.
      ihere. to_implM.
      eapply implM_embed_bind.
      { eapply bn_from_montgomery_word_walk; [exact PRE4| reflexivity| exact (ref_at_stable _ _ _ _ PL _ _ RS14 HAr)| exact (ref_at_stable _ _ _ _ PL _ _ RS4 HAt)
          | exact WRr| rewrite Et; apply wref_pool| exact HPM| reflexivity| reflexivity| reflexivity]. }
      cbv beta. intros [u5 bs5] st5 ms5 PO. apply BPK in PO; [|intros v b o p a [E _]; exact E].
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m5 & OW5 & -> & KP & (_ & ->)).
      destruct (KPOST _ _ _ _ _ _ _ _ _ ENV4 KP) as (ENV5 & LS5). pose proof KP as RS5; apply kpost_refs in RS5.
      cbn [fst snd] in *. clear PRE4 KP.
      replace (ret_pc (Z_to_bv 64 1048512)) with (Z_to_bv 64 1048512) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

      unfold implM. iprefix. step. step. step. step.
      destruct (KPRE _ _ _ _ _ CS ENV5 LS5 LOF) as (errv5 & PRE5).
      ihere. to_implM.
      eapply implM_post_evt.
      { eapply BN_CTX_end_walk; [exact PRE5| reflexivity| exact HPC| reflexivity]. }
      cbv beta. intros [u6 bs6] st6 ms6 PO. apply BPK in PO; [|intros v b o p a [E _]; exact E].
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m6 & OW6 & -> & KP & (_ & EOW6)).
      destruct (KPOST _ _ _ _ _ _ _ _ _ ENV5 KP) as (ENV6 & LS6). pose proof KP as RS6; apply kpost_refs in RS6.
      cbn [fst snd] in *. clear PRE5 KP.
      replace (ret_pc (Z_to_bv 64 1048544)) with (Z_to_bv 64 1048544) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof (kenv_final LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -64) s bs OW m _ _ _ _ _ ENV6) as (F1 & F2 & STF & (errvF & F4) & F5 & F6 & F7 & F8 & F9 & FRF).

      step. do 8 step. release_frame FRF STF (bv_unsigned sp). step. step.
      apply evt_done. unfold bn_post. do 15 eexists. exists m6, OW6, PL, errvF. split; [reflexivity|]. cbn [fst snd].
      split; [exact F1|]. split; [exact LS6|]. split; [exact F2|]. split; [exact STF|]. split; [exact F4|]. split; [exact F5|].
      split; [exact F6|]. split; [exact F7|]. split; [exact F8|]. split; [first [eapply refs_stable_trans; [exact F9| exact RS6] | exact F9]|]. split; reflexivity.
  Qed.

  Lemma BN_mod_mul_montgomery_walk : mont3_stmt BN_MOD_MUL_MONTGOMERY MONT_MUL2_STACK (BN_mod_mul_montgomery (tree_ops bptr)).
  Proof.
    unfold mont3_stmt. intros until qc. intros (HEAP & LS & FROK & AUX & SPB & B63 & ST & CEIL & GLO & LO & ERR & MI) -> SP16 HAr HAa HAb WRr NROb HPM HPC -> -> -> -> ->.
    unfold MONT_MUL2_STACK, BN_MOD_MUL_MONTGOMERY, GLOBALS_TOP, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgusegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3346328 - 164) with 3346164 in ERR.
    assert (GLO' : GLOBALS_TOP <= lo) by exact GLO.

    unfold BN_mod_mul_montgomery, bbind. cbn [bind tree_ops tbind fst snd].
    unfold implM. iprefix.

    carve_frame 32%nat ST. do 7 step. step.
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
    assert (LOF : lo <= bv_unsigned sp + -32 - MONT_MUL_STACK) by (unfold MONT_MUL_STACK; lia).
    clear HEAP AUX ST ERR MI MU WM HWL WOK FR.

    destruct (KPRE _ _ _ _ _ MONT_MUL_STACK ENV LS1 LOF) as (errv1 & PRE1).
    ihere. to_implM.
    eapply implM_embed_bind.
    { eapply bn_mul_mont_fixed_top_walk; [exact PRE1| reflexivity| sp16| exact HAr| exact HAa| exact HAb| exact WRr| exact NROb| exact HPM| exact HPC
        | reflexivity| reflexivity| reflexivity| reflexivity| reflexivity]. }
    cbv beta. intros [u1 bs1] st1 ms1 PO. apply BPK in PO; [|intros v b o p a [E _]; exact E].
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & OW2 & -> & KP & (_ & ->)).
    destruct (KPOST _ _ _ _ _ _ _ _ _ ENV KP) as (ENV2 & LS2). pose proof KP as RS2; apply kpost_refs in RS2.
    cbn [fst snd] in *. clear PRE1 KP ENV LS1.
    replace (ret_pc (Z_to_bv 64 1048260)) with (Z_to_bv 64 1048260) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (ref_at_stable _ _ _ _ PL _ _ RS2 HAr) as HAr2.

    unfold bbind, bget, bset. cbn [bind ret tree_ops tbind fst snd embed interp]. apply implM_interp_ret.
    step. step. step.
    eapply (ctop_call LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -32) s bs OW m CEIL GLO' FBlo FBsp SPB B63 SPR2 FROK);
      [clear - LOF CS16; unfold MONT_MUL_STACK in LOF; lia | exact ENV2 | exact LS2 | exact HAr2 | exact WRr |].
    intros m3 z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 ENV3 LS3.
    replace (ret_pc (Z_to_bv 64 1048272)) with (Z_to_bv 64 1048272) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (kenv_final LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -32) s bs OW m _ _ _ _ _ ENV3) as (F1 & F2 & STF & (errvF & F4) & F5 & F6 & F7 & F8 & F9 & FRF).
    step. do 4 step. release_frame FRF STF (bv_unsigned sp). step. step.
    apply evt_done. unfold bn_post. do 15 eexists. exists m3, OW2, PL, errvF. split; [reflexivity|]. cbn [fst snd].
    split; [exact F1|]. split; [exact LS3|]. split; [exact F2|]. split; [exact STF|]. split; [exact F4|]. split; [exact F5|].
    split; [exact F6|]. split; [exact F7|]. split; [exact F8|]. split; [exact F9|]. split; reflexivity.
  Qed.

  Lemma bn_to_mont_fixed_top_walk : mont2_stmt BN_TO_MONT_FIXED_TOP MONT_MUL_STACK (bn_to_mont_fixed_top (tree_ops bptr)) false.
  Proof.
    unfold mont2_stmt. intros until qc. intros PRE -> SP16 HAr HAa WRr _ HPM HPC -> -> -> ->.
    pose proof PRE as (HEAP & LS & FROK & AUX & SPB & B63 & ST & CEIL & GLO & LO & ERR & MI).
    unfold MONT_MUL_STACK, BN_TO_MONT_FIXED_TOP, GLOBALS_TOP, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgusegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3346328 - 164) with 3346164 in ERR.
    unfold bn_to_mont_fixed_top.
    unfold implM. iprefix.
    destruct (ref_at_ualign_any _ _ _ _ _ _ _ _ _ HEAP PARTS (ref_at_montRR bs OW PL am qm HPM)) as (AM0 & AM8).
    assert (AMR : am < 2^64) by (pose proof (ref_at_range_any _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK (ref_at_montRR bs OW PL am qm HPM)) as (X & Y); clear - X Y; lia).
    carve_frame 16%nat ST. do 4 step. hide_ors. ub_chk. step. zstep. ub_chk. unhide.
    do 3 step. release_frame FR ST (bv_unsigned sp). step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mX end.
    assert (HWL : Forall (w_lib bs OW PL lo (bv_unsigned sp)) [(bv_unsigned sp + -16, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
    assert (WOK : Forall (w_ok OW LB bs PL EA (bv_unsigned sp) []) [(bv_unsigned sp + -16, bv_unsigned sp)]) by (constructor; [apply w_stack; cbn; lia| constructor]).
    ihere. to_implM.
    eapply implM_mono.
    { eapply bn_mul_mont_fixed_top_walk; [| reflexivity| sp16| exact HAr| exact HAa| exact (ref_at_montRR bs OW PL am qm HPM)| exact WRr| exact RMontRR_not_one| exact HPM| exact HPC
        | reflexivity| reflexivity| reflexivity| reflexivity| reflexivity].
      unfold bn_pre, MONT_MUL_STACK.
      split; [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL)|].
      split; [exact (lib_state_frame s LB _ _ [] bs m mX OW PL EA _ HEAP LS MU WM FROK WOK)|].
      split; [exact FROK|]. split; [apply (seg_auxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK AUX MU WM HWL SPB ltac:(lia)); unfold GLOBALS_TOP; lia|].
      split; [exact SPB|]. split; [exact B63|]. split; [exact ST|]. split; [exact CEIL|]. split; [unfold GLOBALS_TOP; lia|]. split; [lia|].
      split; [unfold LX_ERRNO, RATP; exact ERR| the_mi]. }
    cbv beta. intros r st' ms' PO. unfold bn_post in *.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m9 & OW9 & PL9 & errv9 & -> & HEAP9 & LS9 & AUX9 & ST9 & ERR9
                    & MI9 & LXP9 & FA9 & SO9 & RST9 & RES9).
    do 15 eexists. exists m9, OW9, PL9, errv9. split; [reflexivity|]. repeat (split; [assumption|]).
    split; [|repeat (split; [assumption|]); exact RES9].
    eapply lx_pres_trans; [apply (seg_lx_pres _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL); unfold GLOBALS_TOP; lia| exact LXP9].
  Qed.

  Lemma BN_to_montgomery_walk : mont2_stmt BN_TO_MONTGOMERY MONT_MUL2_STACK (BN_to_montgomery (tree_ops bptr)) false.
  Proof.
    unfold mont2_stmt. intros until qc. intros PRE -> SP16 HAr HAa WRr _ HPM HPC -> -> -> ->.
    pose proof PRE as (HEAP & LS & FROK & AUX & SPB & B63 & ST & CEIL & GLO & LO & ERR & MI).
    unfold MONT_MUL2_STACK, BN_TO_MONTGOMERY, GLOBALS_TOP, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgusegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3346328 - 164) with 3346164 in ERR.
    unfold BN_to_montgomery.
    unfold implM. iprefix.
    destruct (ref_at_ualign_any _ _ _ _ _ _ _ _ _ HEAP PARTS (ref_at_montRR bs OW PL am qm HPM)) as (AM0 & AM8).
    assert (AMR : am < 2^64) by (pose proof (ref_at_range_any _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK (ref_at_montRR bs OW PL am qm HPM)) as (X & Y); clear - X Y; lia).
    carve_frame 16%nat ST. do 4 step. hide_ors. ub_chk. step. zstep. ub_chk. unhide.
    do 3 step. release_frame FR ST (bv_unsigned sp). step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mX end.
    assert (HWL : Forall (w_lib bs OW PL lo (bv_unsigned sp)) [(bv_unsigned sp + -16, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
    assert (WOK : Forall (w_ok OW LB bs PL EA (bv_unsigned sp) []) [(bv_unsigned sp + -16, bv_unsigned sp)]) by (constructor; [apply w_stack; cbn; lia| constructor]).
    ihere. to_implM.
    eapply implM_mono.
    { eapply BN_mod_mul_montgomery_walk; [| reflexivity| sp16| exact HAr| exact HAa| exact (ref_at_montRR bs OW PL am qm HPM)| exact WRr| exact RMontRR_not_one| exact HPM| exact HPC
        | reflexivity| reflexivity| reflexivity| reflexivity| reflexivity].
      unfold bn_pre, MONT_MUL2_STACK.
      split; [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL)|].
      split; [exact (lib_state_frame s LB _ _ [] bs m mX OW PL EA _ HEAP LS MU WM FROK WOK)|].
      split; [exact FROK|]. split; [apply (seg_auxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK AUX MU WM HWL SPB ltac:(lia)); unfold GLOBALS_TOP; lia|].
      split; [exact SPB|]. split; [exact B63|]. split; [exact ST|]. split; [exact CEIL|]. split; [unfold GLOBALS_TOP; lia|]. split; [lia|].
      split; [unfold LX_ERRNO, RATP; exact ERR| the_mi]. }
    cbv beta. intros r st' ms' PO. unfold bn_post in *.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m9 & OW9 & PL9 & errv9 & -> & HEAP9 & LS9 & AUX9 & ST9 & ERR9
                    & MI9 & LXP9 & FA9 & SO9 & RST9 & RES9).
    do 15 eexists. exists m9, OW9, PL9, errv9. split; [reflexivity|]. repeat (split; [assumption|]).
    split; [|repeat (split; [assumption|]); exact RES9].
    eapply lx_pres_trans; [apply (seg_lx_pres _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL); unfold GLOBALS_TOP; lia| exact LXP9].
  Qed.

  Lemma bn_from_mont_fixed_top_walk : mont2_stmt BN_FROM_MONT_FIXED_TOP MONT_MUL_STACK (bn_from_mont_fixed_top (tree_ops bptr)) true.
  Proof.
    unfold mont2_stmt. intros until qc. intros (HEAP & LS & FROK & AUX & SPB & B63 & ST & CEIL & GLO & LO & ERR & MI) -> SP16 HAr HAa WRr NROa HPM HPC -> -> -> ->.
    specialize (NROa eq_refl).
    unfold MONT_MUL_STACK, BN_FROM_MONT_FIXED_TOP, GLOBALS_TOP, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgusegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3346328 - 164) with 3346164 in ERR.
    assert (GLO' : GLOBALS_TOP <= lo) by exact GLO.

    unfold bn_from_mont_fixed_top, bbind. cbn [bind tree_ops tbind fst snd].
    unfold implM. iprefix.

    carve_frame 64%nat ST. do 14 step. step.
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
    replace (ret_pc (Z_to_bv 64 1049420)) with (Z_to_bv 64 1049420) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

    unfold implM. iprefix. step. step.
    destruct (KPRE _ _ _ _ _ CS ENV2 LS2 LOF) as (errv2 & PRE2).
    ihere. to_implM.
    eapply implM_embed_bind.
    { eapply BN_CTX_get_walk; [exact PRE2| reflexivity| exact HPC| reflexivity]. }
    cbv beta. intros [t bs2] st2 ms2 PO. apply BPK in PO; [|intros v b o p a [E _]; exact E].
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m3 & OW3 & -> & KP & (_ & (ti & Et) & (at_ & HAt & ->) & INCL3)).
    destruct (KPOST _ _ _ _ _ _ _ _ _ ENV2 KP) as (ENV3 & LS3). pose proof KP as RS3; apply kpost_refs in RS3.
    cbn [fst snd] in *. clear PRE2 KP ENV2 LS2.
    replace (ret_pc (Z_to_bv 64 1049428)) with (Z_to_bv 64 1049428) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

    pose proof (refs_stable_trans _ _ _ _ _ _ RS2 RS3) as RS13.
    pose proof (ref_at_stable _ _ _ _ PL _ _ RS13 HAr) as HAr3. pose proof (ref_at_stable _ _ _ _ PL _ _ RS13 HAa) as HAa3.
    pose proof ENV3 as (HEAP3 & _). pose proof (lib_state_h_parts _ _ _ _ _ _ LS3) as PARTS3.
    assert (FROK3 : frames_ok PL (bv_unsigned sp + -64) B) by (eapply frames_ok_call; [exact FROK| exact CEIL| exact FBlo| exact FBsp]).
    assert (NROt : t <> ROne) by (rewrite Et; unfold RPool, ROne, NFIX; lia).
    pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP3 PARTS3 FROK3 HAt NROt) as (At0 & AtC & _).
    assert (AtR : 0 < at_ < 2^64) by (clear - At0 AtC SPR; lia). clear AtC.

    unfold implM. iprefix.
    step. if_cases KZ; rewrite ?unsigned_lit in KZ by (clear - AtR; lia); zify_cond KZ; [exfalso; clear - KZ AtR; lia| clear KZ].
    step. step. step.
    destruct (KPRE _ _ _ _ _ CS ENV3 LS3 LOF) as (errv3 & PRE3).
    ihere. to_implM.
    eapply implM_embed_bind.
    { eapply BN_copy_walk; [exact PRE3| reflexivity| exact HAt| exact HAa3| rewrite Et; apply wref_pool| exact NROa| reflexivity| reflexivity]. }
    cbv beta. intros [u4 bs4] st4 ms4 PO. apply BPK in PO; [|intros v b o p a [E _]; exact E].
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m4 & OW4 & -> & KP & (_ & -> & _)).
    destruct (KPOST _ _ _ _ _ _ _ _ _ ENV3 KP) as (ENV4 & LS4). pose proof KP as RS4; apply kpost_refs in RS4.
    cbn [fst snd] in *. clear PRE3 KP.
    replace (ret_pc (Z_to_bv 64 1049444)) with (Z_to_bv 64 1049444) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

    unfold implM. iprefix.
    step. if_cases KZ; rewrite ?unsigned_lit in KZ by (clear - AtR; lia); zify_cond KZ; [exfalso; clear - KZ AtR; lia| clear KZ].
    step. step. step. step.
    destruct (KPRE _ _ _ _ _ CS ENV4 LS4 LOF) as (errv4 & PRE4).
    pose proof (refs_stable_trans _ _ _ _ _ _ RS13 RS4) as RS14.
    ihere. to_implM.
    eapply implM_embed_bind.
    { eapply bn_from_montgomery_word_walk; [exact PRE4| reflexivity| exact (ref_at_stable _ _ _ _ PL _ _ RS14 HAr)| exact (ref_at_stable _ _ _ _ PL _ _ RS4 HAt)
        | exact WRr| rewrite Et; apply wref_pool| exact HPM| reflexivity| reflexivity| reflexivity]. }
    cbv beta. intros [u5 bs5] st5 ms5 PO. apply BPK in PO; [|intros v b o p a [E _]; exact E].
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m5 & OW5 & -> & KP & (_ & ->)).
    destruct (KPOST _ _ _ _ _ _ _ _ _ ENV4 KP) as (ENV5 & LS5). pose proof KP as RS5; apply kpost_refs in RS5.
    cbn [fst snd] in *. clear PRE4 KP.
    replace (ret_pc (Z_to_bv 64 1049464)) with (Z_to_bv 64 1049464) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

    unfold implM. iprefix. step. step. step. step.
    destruct (KPRE _ _ _ _ _ CS ENV5 LS5 LOF) as (errv5 & PRE5).
    ihere. to_implM.
    eapply implM_post_evt.
    { eapply BN_CTX_end_walk; [exact PRE5| reflexivity| exact HPC| reflexivity]. }
    cbv beta. intros [u6 bs6] st6 ms6 PO. apply BPK in PO; [|intros v b o p a [E _]; exact E].
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m6 & OW6 & -> & KP & (_ & EOW6)).
    destruct (KPOST _ _ _ _ _ _ _ _ _ ENV5 KP) as (ENV6 & LS6). pose proof KP as RS6; apply kpost_refs in RS6.
    cbn [fst snd] in *. clear PRE5 KP.
    replace (ret_pc (Z_to_bv 64 1049484)) with (Z_to_bv 64 1049484) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (kenv_final LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -64) s bs OW m _ _ _ _ _ ENV6) as (F1 & F2 & STF & (errvF & F4) & F5 & F6 & F7 & F8 & F9 & FRF).

    step. do 7 step. release_frame FRF STF (bv_unsigned sp). step. step.
    apply evt_done. unfold bn_post. do 15 eexists. exists m6, OW6, PL, errvF. split; [reflexivity|]. cbn [fst snd].
    split; [exact F1|]. split; [exact LS6|]. split; [exact F2|]. split; [exact STF|]. split; [exact F4|]. split; [exact F5|].
    split; [exact F6|]. split; [exact F7|]. split; [exact F8|]. split; [first [eapply refs_stable_trans; [exact F9| exact RS6] | exact F9]|]. split; reflexivity.
  Qed.

  Lemma BN_from_montgomery_walk : mont2_stmt BN_FROM_MONTGOMERY MONT_MUL2_STACK (BN_from_montgomery (tree_ops bptr)) true.
  Proof.
    unfold mont2_stmt. intros until qc. intros (HEAP & LS & FROK & AUX & SPB & B63 & ST & CEIL & GLO & LO & ERR & MI) -> SP16 HAr HAa WRr NROa HPM HPC -> -> -> ->.
    unfold MONT_MUL2_STACK, BN_FROM_MONTGOMERY, GLOBALS_TOP, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgusegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3346328 - 164) with 3346164 in ERR.
    assert (GLO' : GLOBALS_TOP <= lo) by exact GLO.

    unfold BN_from_montgomery, bbind. cbn [bind tree_ops tbind fst snd].
    unfold implM. iprefix.

    carve_frame 32%nat ST. do 7 step. step.
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
    assert (LOF : lo <= bv_unsigned sp + -32 - MONT_MUL_STACK) by (unfold MONT_MUL_STACK; lia).
    clear HEAP AUX ST ERR MI MU WM HWL WOK FR.

    destruct (KPRE _ _ _ _ _ MONT_MUL_STACK ENV LS1 LOF) as (errv1 & PRE1).
    ihere. to_implM.
    eapply implM_embed_bind.
    { eapply bn_from_mont_fixed_top_walk; [exact PRE1| reflexivity| sp16| exact HAr| exact HAa| exact WRr| intros _; exact (NROa eq_refl)| exact HPM| exact HPC
        | reflexivity| reflexivity| reflexivity| reflexivity]. }
    cbv beta. intros [u1 bs1] st1 ms1 PO. apply BPK in PO; [|intros v b o p a [E _]; exact E].
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & OW2 & -> & KP & (_ & ->)).
    destruct (KPOST _ _ _ _ _ _ _ _ _ ENV KP) as (ENV2 & LS2). pose proof KP as RS2; apply kpost_refs in RS2.
    cbn [fst snd] in *. clear PRE1 KP ENV LS1.
    replace (ret_pc (Z_to_bv 64 1049320)) with (Z_to_bv 64 1049320) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (ref_at_stable _ _ _ _ PL _ _ RS2 HAr) as HAr2.

    unfold bbind, bget, bset. cbn [bind ret tree_ops tbind fst snd embed interp]. apply implM_interp_ret.
    step. step. step.
    eapply (ctop_call LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -32) s bs OW m CEIL GLO' FBlo FBsp SPB B63 SPR2 FROK);
      [clear - LOF CS16; unfold MONT_MUL_STACK in LOF; lia | exact ENV2 | exact LS2 | exact HAr2 | exact WRr |].
    intros m3 z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 ENV3 LS3.
    replace (ret_pc (Z_to_bv 64 1049332)) with (Z_to_bv 64 1049332) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (kenv_final LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -32) s bs OW m _ _ _ _ _ ENV3) as (F1 & F2 & STF & (errvF & F4) & F5 & F6 & F7 & F8 & F9 & FRF).
    step. do 4 step. release_frame FRF STF (bv_unsigned sp). step. step.
    apply evt_done. unfold bn_post. do 15 eexists. exists m3, OW2, PL, errvF. split; [reflexivity|]. cbn [fst snd].
    split; [exact F1|]. split; [exact LS3|]. split; [exact F2|]. split; [exact STF|]. split; [exact F4|]. split; [exact F5|].
    split; [exact F6|]. split; [exact F7|]. split; [exact F8|]. split; [exact F9|]. split; reflexivity.
  Qed.

End Proofs.

End WithCeiling0.
