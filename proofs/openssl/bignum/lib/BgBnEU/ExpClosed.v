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
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnDivWords BnModel BnTree BnInv BnBridge BgState BgWords BgInv BgLib BgArith BgMont BgExp.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Import Layout Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnMem BnTac BnTacX.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require Import BnHeap W_small W_small2 W_top.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU2 Require Import W_small3.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require BnRep.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgRepU Require Import BgRepDefs BgRep BgLayer BgIface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnRU Require W_ctx W_ctx_get W_ctx_end W_bndiv W_add W_expand W_copy W_cmp W_usub.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnRU2 Require W_sub W_sqr W_mul W_mul_top W_set_word W_set_bit W_shift W_add_word W_mul_word.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnEU Require W_nnmod W_mod_mul W_exp_simple W_recp_set W_div_recp W_recp W_recp_free W_exp_recp W_mont W_from_mont W_exp_mont W_exp_mont_g W_exp_mont_word.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnRU2 Require InvClosed.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnEU Require W_mont_set_b W_mont_set.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnEU Require Import W_mod_exp.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Rnd.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Lemma bn_pre_wk : forall s bs m OW LB PL EA sp lo B errv K K',
  bn_pre s bs m OW LB PL EA sp lo B errv K' -> K <= K' -> bn_pre s bs m OW LB PL EA sp lo B errv K.
Proof.
  intros s bs m OW LB PL EA sp lo B errv K K' (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12) H.
  unfold bn_pre. repeat (split; [assumption|]). split; [lia|]. split; assumption.
Qed.

Lemma bn_post_mono : forall {A : Type} (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (bs : bstate bptr) (OW LB : list block) (lo B : Z) (m : mem) (PL : placement) (EA : BgBnU.BnRep.err_addrs)
    (RES RES' : A -> bstate bptr -> list block -> placement -> word -> Prop) (r : A * bstate bptr) (st' : PState) (ms' : machine_state),
  (forall v bs' OW' PL' a0', RES v bs' OW' PL' a0' -> RES' v bs' OW' PL' a0') ->
  bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA RES r st' ms' ->
  bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA RES' r st' ms'.
Proof.
  intros until ms'. intros HR PO. unfold bn_post in *.
  destruct PO as (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & OW' & PL' & errv' & E & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11).
  exists t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m', OW', PL', errv'.
  split; [exact E|]. split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P5|]. split; [exact P6|].
  split; [exact P7|]. split; [exact P8|]. split; [exact P9|]. split; [exact P10|]. apply HR. exact P11.
Qed.

Lemma mont3_wk : forall (E K K' : Z) f, W_mont.mont3_stmt E K f -> K <= K' -> W_mont.mont3_stmt E K' f.
Proof.
  intros E K K' f H HK. unfold W_mont.mont3_stmt in *. intros until qc. intros PRE. eapply H. exact (bn_pre_wk _ _ _ _ _ _ _ _ _ _ _ _ _ PRE HK).
Qed.

Lemma mont2_wk : forall (E K K' : Z) f nro, W_mont.mont2_stmt E K f nro -> K <= K' -> W_mont.mont2_stmt E K' f nro.
Proof.
  intros E K K' f nro H HK. unfold W_mont.mont2_stmt in *. intros until qc. intros PRE. eapply H. exact (bn_pre_wk _ _ _ _ _ _ _ _ _ _ _ _ _ PRE HK).
Qed.

Lemma exp_stmt_f_wk : forall (E K K' : Z) one sixth, exp_stmt_f E K one sixth -> K <= K' -> exp_stmt_f E K' one sixth.
Proof.
  intros E K K' one sixth H HK. unfold exp_stmt_f in *. intros until qc. intros PRE. eapply H. exact (bn_pre_wk _ _ _ _ _ _ _ _ _ _ _ _ _ PRE HK).
Qed.

Section Closed.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Local Tactic Notation "apw" uconstr(L) := first [eapply (L HM HF) | eapply (L HM) | eapply (L HF) | eapply L].

  Definition NNMOD_CS : Z := W_bndiv.BN_DIV_TOP_STACK.
  Definition NNMOD_STACK : Z := 32 + NNMOD_CS.

  Lemma BN_nnmod_closed : forall (CS : Z), NNMOD_STACK <= CS -> forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BgBnU.BnRep.err_addrs)
      (lo B : Z) (errv : word) (rr rx rm : bnref) (ar ax am ac : Z) (qc : bptr),
    bn_pre s bs m OW LB PL EA sp lo B errv CS -> tp = wz RATP ->
    ref_at bs OW PL rr ar -> ref_at bs OW PL rx ax -> ref_at bs OW PL rm am -> hpl PL rr -> rx <> ROne -> rm <> ROne -> pl_ctx PL = Some (ac, qc) ->
    a0 = wz ar -> a1 = wz ax -> a2 = wz am -> a3 = wz ac ->
    implM bgusegs (interp (embed (BN_nnmod (tree_ops bptr) rr rx rm bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz W_exp_simple.BN_NNMOD) fc None m (seg_rom bgusegs)).
  Proof.
    intros CS HCS. intros until qc. intros PRE.
    eapply (W_nnmod.BN_nnmod_walk NNMOD_CS); [vm_compute; intros XXc; discriminate XXc| | | | exact (bn_pre_wk _ _ _ _ _ _ _ _ _ _ _ _ _ PRE HCS)].
    -
      intros until qc0. intros PRE1 -> HA1 HA2 HA3 HP1 N2 N3 HC1 -> -> -> -> ->.
      eapply (W_bndiv.BN_div_walk HM HF) with (dv := None) (rm := Some rr0);
        [exact PRE1| reflexivity| exact HC1| reflexivity| exact HA1| exact HA2| exact HA3| intros d X; discriminate X| intros r X; injection X as <-; exact HP1| exact N2| exact N3
        | reflexivity| reflexivity| reflexivity| reflexivity| reflexivity].
    - intros until Y. intros PRE1.
      apw W_add.BN_add_walk. eapply bn_pre_wk; [exact PRE1|]. vm_compute; intros XXc; discriminate XXc.
    - intros until Y. intros PRE1.
      apw W_sub.BN_sub_walk. eapply bn_pre_wk; [exact PRE1|]. vm_compute; intros XXc; discriminate XXc.
  Qed.

  Local Ltac cle := vm_compute; intros XXc; discriminate XXc.

  Definition MODMUL_CS : Z := NNMOD_STACK.
  Definition MODMUL_STACK : Z := 64 + MODMUL_CS.

  Lemma BN_mod_mul_closed : forall (CS : Z), MODMUL_STACK <= CS -> forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BgBnU.BnRep.err_addrs)
      (lo B : Z) (errv : word) (rr ra_ rb rm : bnref) (arr ara arb arm ac : Z) (qc : bptr),
    bn_pre s bs m OW LB PL EA sp lo B errv CS -> tp = wz RATP -> bv_unsigned sp mod 16 = 0 ->
    ref_at bs OW PL rr arr -> ref_at bs OW PL ra_ ara -> ref_at bs OW PL rb arb -> ref_at bs OW PL rm arm ->
    hpl PL rr -> ra_ <> ROne -> rb <> ROne -> rm <> ROne -> pl_ctx PL = Some (ac, qc) ->
    a0 = wz arr -> a1 = wz ara -> a2 = wz arb -> a3 = wz arm -> a4 = wz ac ->
    implM bgusegs (interp (embed (BN_mod_mul (tree_ops bptr) rr ra_ rb rm bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz W_exp_simple.BN_MOD_MUL) fc None m (seg_rom bgusegs)).
  Proof.
    intros CS HCS. intros until qc. intros PRE.
    eapply (W_mod_mul.BN_mod_mul_walk MODMUL_CS); [cle| | | | | | | exact (bn_pre_wk _ _ _ _ _ _ _ _ _ _ _ _ _ PRE HCS)].
    - intros until qc0. intros PRE1. apw W_ctx.BN_CTX_start_walk. eapply bn_pre_wk; [exact PRE1| cle].
    - intros until qc0. intros PRE1. apw W_ctx_get.BN_CTX_get_walk. eapply bn_pre_wk; [exact PRE1| cle].
    - intros until qc0. intros PRE1. apw W_ctx_end.BN_CTX_end_walk. eapply bn_pre_wk; [exact PRE1| cle].
    - intros until qc0. intros PRE1. apw W_sqr.BN_sqr_walk. eapply bn_pre_wk; [exact PRE1| cle].
    - intros until qc0. intros PRE1 T1 H1 H2 H3 HP1 NX NY HC1 E0 E1 E2 E3.
      first [eapply (W_mul_top.BN_mul_walk_cs HM HF MODMUL_CS ltac:(cle)) | eapply (W_mul_top.BN_mul_walk_cs HM MODMUL_CS ltac:(cle))]; [exact PRE1| exact T1| exact H1| exact H2| exact H3| exact HP1| exact NY| exact HC1| exact E0| exact E1| exact E2| exact E3].
    - eapply (BN_nnmod_closed MODMUL_CS). cle.
  Qed.

  Definition SIMPLE_CS : Z := MODMUL_STACK.
  Definition SIMPLE_STACK : Z := 368 + SIMPLE_CS.

  Lemma BN_mod_exp_simple_closed : exp_stmt W_exp_simple.BN_MOD_EXP_SIMPLE SIMPLE_STACK (BN_mod_exp_simple (tree_ops bptr)) None.
  Proof.
    eapply (W_exp_simple.BN_mod_exp_simple_walk SIMPLE_CS); [cle| | | | | |].
    - intros until qc. intros PRE1. apw W_ctx.BN_CTX_start_walk. eapply bn_pre_wk; [exact PRE1| cle].
    - intros until qc. intros PRE1. apw W_ctx_get.BN_CTX_get_walk. eapply bn_pre_wk; [exact PRE1| cle].
    - intros until qc. intros PRE1. apw W_ctx_end.BN_CTX_end_walk. eapply bn_pre_wk; [exact PRE1| cle].
    - eapply (BN_nnmod_closed SIMPLE_CS). cle.
    - eapply (BN_mod_mul_closed SIMPLE_CS). cle.
    - intros until w. intros PRE1 T1 H1 W1 R1 E0 E1.
      first [eapply (W_set_word.BN_set_word_walk HM HF) | eapply (W_set_word.BN_set_word_walk HM)]; [eapply bn_pre_wk; [exact PRE1| cle]| exact T1| exact H1| exact W1| exact E0| exact E1| exact R1].
  Qed.

  Definition RECPSET_CS : Z := W_copy.BN_COPY_STACK.
  Definition RECPSET_STACK : Z := 32 + RECPSET_CS.
  Lemma BN_RECP_CTX_set_closed : forall (CS : Z), RECPSET_STACK <= CS -> forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BgBnU.BnRep.err_addrs)
      (lo B : Z) (errv : word) (rd : bnref) (ad an : Z),
    bn_pre s bs m OW LB PL EA sp lo B errv CS -> tp = wz RATP ->
    ref_at bs OW PL rd ad -> rd <> ROne -> recp_at PL an -> a0 = wz an -> a1 = wz ad ->
    implM bgusegs (interp (embed (BN_RECP_CTX_set (tree_ops bptr) rd bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz W_exp_recp.BN_RECP_CTX_SET) fc None m (seg_rom bgusegs)).
  Proof.
    intros CS HCS. intros until an. intros PRE.
    eapply (W_recp_set.BN_RECP_CTX_set_walk RECPSET_CS); [cle| | exact (bn_pre_wk _ _ _ _ _ _ _ _ _ _ _ _ _ PRE HCS)].
    intros until ay. intros PRE1. apw W_copy.BN_copy_walk. eapply bn_pre_wk; [exact PRE1| cle].
  Qed.

  Definition RECIP_CS : Z := W_bndiv.BN_DIV_TOP_STACK.
  Definition RECIP_STACK : Z := 64 + RECIP_CS.
  Lemma BN_reciprocal_closed : forall (CS : Z), RECIP_STACK <= CS -> forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BgBnU.BnRep.err_addrs)
      (lo B : Z) (errv : word) (rr rm : bnref) (arr arm len ac : Z) (qc : bptr),
    bn_pre s bs m OW LB PL EA sp lo B errv CS -> tp = wz RATP ->
    ref_at bs OW PL rr arr -> ref_at bs OW PL rm arm -> wref PL rr -> rm <> ROne -> pl_ctx PL = Some (ac, qc) -> 0 <= len < 2^31 ->
    a0 = wz arr -> a1 = wz arm -> a2 = wz len -> a3 = wz ac ->
    implM bgusegs (interp (embed (BN_reciprocal (tree_ops bptr) rr rm len bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (fun r _ _ PL' a0' => PL' = PL /\ r = len /\ a0' = wz len))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz W_div_recp.BN_RECIPROCAL) fc None m (seg_rom bgusegs)).
  Proof.
    intros CS HCS. intros until qc. intros PRE.
    eapply (W_recp_set.BN_reciprocal_walk RECIP_CS); [cle| | | | | | exact (bn_pre_wk _ _ _ _ _ _ _ _ _ _ _ _ _ PRE HCS)].
    - intros until qc0. intros PRE1. apw W_ctx.BN_CTX_start_walk. eapply bn_pre_wk; [exact PRE1| cle].
    - intros until qc0. intros PRE1. apw W_ctx_get.BN_CTX_get_walk. eapply bn_pre_wk; [exact PRE1| cle].
    - intros until qc0. intros PRE1. apw W_ctx_end.BN_CTX_end_walk. eapply bn_pre_wk; [exact PRE1| cle].
    - intros until n. intros PRE1. apw W_set_bit.BN_set_bit_walk. eapply bn_pre_wk; [exact PRE1| cle].
    -
      intros until qc0. intros PRE1 -> HA1 HA2 HA3 HW1 N2 N3 HC1 -> -> -> -> ->.
      eapply (W_bndiv.BN_div_walk HM HF) with (dv := Some rr0) (rm := None);
        [eapply bn_pre_wk; [exact PRE1| cle]| reflexivity| exact HC1| exact HA1| reflexivity| exact HA2| exact HA3| intros d X; injection X as <-; exact HW1| intros r X; discriminate X| exact N2| exact N3
        | reflexivity| reflexivity| reflexivity| reflexivity| reflexivity].
  Qed.

  Definition DIVRECP_CS : Z := RECIP_STACK.
  Definition DIVRECP_STACK : Z := 96 + DIVRECP_CS.
  Lemma BN_div_recp_closed : forall (CS : Z), DIVRECP_STACK <= CS -> forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BgBnU.BnRep.err_addrs)
      (lo B : Z) (errv : word) (rr rm : bnref) (ar am an ac : Z) (qc : bptr),
    bn_pre s bs m OW LB PL EA sp lo B errv CS -> tp = wz RATP ->
    ref_at bs OW PL rr ar -> ref_at bs OW PL rm am -> hpl PL rr -> rm <> ROne -> recp_at PL an -> pl_ctx PL = Some (ac, qc) ->
    a0 = wz 0 -> a1 = wz ar -> a2 = wz am -> a3 = wz an -> a4 = wz ac ->
    implM bgusegs (interp (embed (BN_div_recp (tree_ops bptr) None (Some rr) rm bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz W_recp.BN_DIV_RECP) fc None m (seg_rom bgusegs)).
  Proof.
    intros CS HCS. intros until qc. intros PRE.
    eapply (W_div_recp.BN_div_recp_walk DIVRECP_CS); [cle| | | | | | | | | | | exact (bn_pre_wk _ _ _ _ _ _ _ _ _ _ _ _ _ PRE HCS)].
    - intros until qc0. intros PRE1. apw W_ctx.BN_CTX_start_walk. eapply bn_pre_wk; [exact PRE1| cle].
    - intros until qc0. intros PRE1. apw W_ctx_get.BN_CTX_get_walk. eapply bn_pre_wk; [exact PRE1| cle].
    - intros until qc0. intros PRE1. apw W_ctx_end.BN_CTX_end_walk. eapply bn_pre_wk; [exact PRE1| cle].
    - intros until b. intros PRE1. apw W_cmp.BN_ucmp_walk. eapply bn_pre_wk; [exact PRE1| cle].
    - intros until ay. intros PRE1. apw W_copy.BN_copy_walk. eapply bn_pre_wk; [exact PRE1| cle].
    - eapply (BN_reciprocal_closed DIVRECP_CS). cle.
    -
      intros until n. intros PRE1 T1 H1 HP1 H2 N2 E0 E1 E2 RN.
      eapply implM_mono.
      { apw W_shift.BN_rshift_walk; [eapply bn_pre_wk; [exact PRE1| cle]| exact T1| exact H1| exact HP1| exact H2| exact N2| exact E0| exact E1| exact E2| clear - RN; lia]. }
      intros r st' ms' PO. eapply bn_post_mono; [|exact PO]. intros v b o p a (X1 & X2 & _). split; assumption.
    - intros until qc0. intros PRE1 T1 H1 H2 H3 HP1 NX NY HC1 E0 E1 E2 E3.
      first [eapply (W_mul_top.BN_mul_walk_cs HM HF DIVRECP_CS ltac:(cle)) | eapply (W_mul_top.BN_mul_walk_cs HM DIVRECP_CS ltac:(cle))]; [exact PRE1| exact T1| exact H1| exact H2| exact H3| exact HP1| exact NY| exact HC1| exact E0| exact E1| exact E2| exact E3].
    - intros until Y. intros PRE1. apw W_usub.BN_usub_walk. eapply bn_pre_wk; [exact PRE1| cle].
    - intros until w. intros PRE1. apw W_add_word.BN_add_word_walk. eapply bn_pre_wk; [exact PRE1| cle].
  Qed.

  Definition MODMULRECP_CS : Z := DIVRECP_STACK.
  Definition MODMULRECP_STACK : Z := 64 + MODMULRECP_CS.
  Lemma BN_mod_mul_reciprocal_closed : forall (CS : Z), MODMULRECP_STACK <= CS -> forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BgBnU.BnRep.err_addrs)
      (lo B : Z) (errv : word) (rr rx ry : bnref) (ar ax ay an ac : Z) (qc : bptr),
    bn_pre s bs m OW LB PL EA sp lo B errv CS -> tp = wz RATP -> bv_unsigned sp mod 16 = 0 ->
    ref_at bs OW PL rr ar -> ref_at bs OW PL rx ax -> ref_at bs OW PL ry ay -> hpl PL rr -> rx <> ROne -> ry <> ROne ->
    recp_at PL an -> pl_ctx PL = Some (ac, qc) ->
    a0 = wz ar -> a1 = wz ax -> a2 = wz ay -> a3 = wz an -> a4 = wz ac ->
    implM bgusegs (interp (embed (BN_mod_mul_reciprocal (tree_ops bptr) rr rx ry bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz W_exp_recp.BN_MOD_MUL_RECIPROCAL) fc None m (seg_rom bgusegs)).
  Proof.
    intros CS HCS. intros until qc. intros PRE.
    pose proof (W_recp.BN_mod_mul_reciprocal_walk MODMULRECP_CS) as HW. unfold W_recp.recp3_stmt in HW.
    eapply HW; [cle| | | | | | | exact (bn_pre_wk _ _ _ _ _ _ _ _ _ _ _ _ _ PRE HCS)]; clear HW.
    - intros until qc0. intros PRE1. apw W_ctx.BN_CTX_start_walk. eapply bn_pre_wk; [exact PRE1| cle].
    - intros until qc0. intros PRE1. apw W_ctx_get.BN_CTX_get_walk. eapply bn_pre_wk; [exact PRE1| cle].
    - intros until qc0. intros PRE1. apw W_ctx_end.BN_CTX_end_walk. eapply bn_pre_wk; [exact PRE1| cle].
    - intros until qc0. intros PRE1. apw W_sqr.BN_sqr_walk. eapply bn_pre_wk; [exact PRE1| cle].
    - intros until qc0. intros PRE1 T1 H1 H2 H3 HP1 NX NY HC1 E0 E1 E2 E3.
      first [eapply (W_mul_top.BN_mul_walk_cs HM HF MODMULRECP_CS ltac:(cle)) | eapply (W_mul_top.BN_mul_walk_cs HM MODMULRECP_CS ltac:(cle))]; [exact PRE1| exact T1| exact H1| exact H2| exact H3| exact HP1| exact NY| exact HC1| exact E0| exact E1| exact E2| exact E3].
    - eapply (BN_div_recp_closed MODMULRECP_CS). cle.
  Qed.

  Definition EXPRECP_CS : Z := MODMULRECP_STACK.
  Definition RECP_STACK : Z := 432 + EXPRECP_CS.

  Lemma BN_mod_exp_recp_closed : exp_stmt_f BN_MOD_EXP_RECP RECP_STACK (BN_mod_exp_recp (tree_ops bptr)) None.
  Proof.
    eapply (W_exp_recp.BN_mod_exp_recp_walk EXPRECP_CS); [cle| | | | | | | | |].
    - intros until qc. intros PRE1. apw W_ctx_end.BN_CTX_end_walk. eapply bn_pre_wk; [exact PRE1| cle].
    - intros until qc. intros PRE1. apw W_ctx_get.BN_CTX_get_walk. eapply bn_pre_wk; [exact PRE1| cle].
    - eapply (BN_mod_mul_reciprocal_closed EXPRECP_CS). cle.
    - intros until pad. intros PRE1. eapply (W_recp_free.BN_RECP_CTX_free_lwalk_cs HF EXPRECP_CS); [cle| exact PRE1].
    - intros until w. intros PRE1 T1 H1 W1 R1 E0 E1.
      first [eapply (W_set_word.BN_set_word_walk HM HF) | eapply (W_set_word.BN_set_word_walk HM)]; [eapply bn_pre_wk; [exact PRE1| cle]| exact T1| exact H1| exact W1| exact E0| exact E1| exact R1].
    - intros until qc. intros PRE1. apw W_ctx.BN_CTX_start_walk. eapply bn_pre_wk; [exact PRE1| cle].
    - intros until ay. intros PRE1. apw W_copy.BN_copy_walk. eapply bn_pre_wk; [exact PRE1| cle].
    - eapply (BN_RECP_CTX_set_closed EXPRECP_CS). cle.
    - eapply (BN_nnmod_closed EXPRECP_CS). cle.
  Qed.

  Definition MONT_CS : Z := W_mul.BN_MUL_FIXED_STACK.
  Definition MONT3_STACK : Z := W_mont.MONT_MUL_STACK MONT_CS.
  Definition MONT2_STACK : Z := W_mont.MONT_MUL2_STACK MONT_CS.

  Lemma bn_mul_mont_fixed_top_closed : W_mont.mont3_stmt W_mont.BN_MUL_MONT_FIXED_TOP MONT3_STACK (bn_mul_mont_fixed_top (tree_ops bptr)).
  Proof.
    eapply (W_mont.bn_mul_mont_fixed_top_walk MONT_CS); [cle| | | | | |].
    - intros until qc. intros PRE1. apw W_ctx.BN_CTX_start_walk. eapply bn_pre_wk; [exact PRE1| cle].
    - intros until qc. intros PRE1. apw W_ctx_get.BN_CTX_get_walk. eapply bn_pre_wk; [exact PRE1| cle].
    - intros until qc. intros PRE1. apw W_ctx_end.BN_CTX_end_walk. eapply bn_pre_wk; [exact PRE1| cle].
    - intros until qc. intros PRE1. eapply (W_sqr.bn_sqr_fixed_top_walk_cs HM HF MONT_CS); [cle| exact PRE1].
    - intros until qc. intros PRE1. eapply (W_mul.bn_mul_fixed_top_walk_cs HM HF MONT_CS); [cle| exact PRE1].
    - intros until qm. intros PRE1. eapply (W_from_mont.bn_from_montgomery_word_walk HM HF). eapply bn_pre_wk; [exact PRE1| cle].
  Qed.

  Lemma BN_mod_mul_montgomery_closed : W_mont.mont3_stmt W_mont.BN_MOD_MUL_MONTGOMERY MONT2_STACK (BN_mod_mul_montgomery (tree_ops bptr)).
  Proof.
    eapply (W_mont.BN_mod_mul_montgomery_walk MONT_CS); [cle| | | | | |].
    - intros until qc. intros PRE1. apw W_ctx.BN_CTX_start_walk. eapply bn_pre_wk; [exact PRE1| cle].
    - intros until qc. intros PRE1. apw W_ctx_get.BN_CTX_get_walk. eapply bn_pre_wk; [exact PRE1| cle].
    - intros until qc. intros PRE1. apw W_ctx_end.BN_CTX_end_walk. eapply bn_pre_wk; [exact PRE1| cle].
    - intros until qc. intros PRE1. eapply (W_sqr.bn_sqr_fixed_top_walk_cs HM HF MONT_CS); [cle| exact PRE1].
    - intros until qc. intros PRE1. eapply (W_mul.bn_mul_fixed_top_walk_cs HM HF MONT_CS); [cle| exact PRE1].
    - intros until qm. intros PRE1. eapply (W_from_mont.bn_from_montgomery_word_walk HM HF). eapply bn_pre_wk; [exact PRE1| cle].
  Qed.

  Lemma bn_to_mont_fixed_top_closed : W_mont.mont2_stmt W_mont.BN_TO_MONT_FIXED_TOP MONT3_STACK (bn_to_mont_fixed_top (tree_ops bptr)) false.
  Proof.
    eapply (W_mont.bn_to_mont_fixed_top_walk MONT_CS); [cle| | | | | |].
    - intros until qc. intros PRE1. apw W_ctx.BN_CTX_start_walk. eapply bn_pre_wk; [exact PRE1| cle].
    - intros until qc. intros PRE1. apw W_ctx_get.BN_CTX_get_walk. eapply bn_pre_wk; [exact PRE1| cle].
    - intros until qc. intros PRE1. apw W_ctx_end.BN_CTX_end_walk. eapply bn_pre_wk; [exact PRE1| cle].
    - intros until qc. intros PRE1. eapply (W_sqr.bn_sqr_fixed_top_walk_cs HM HF MONT_CS); [cle| exact PRE1].
    - intros until qc. intros PRE1. eapply (W_mul.bn_mul_fixed_top_walk_cs HM HF MONT_CS); [cle| exact PRE1].
    - intros until qm. intros PRE1. eapply (W_from_mont.bn_from_montgomery_word_walk HM HF). eapply bn_pre_wk; [exact PRE1| cle].
  Qed.

  Lemma BN_to_montgomery_closed : W_mont.mont2_stmt W_mont.BN_TO_MONTGOMERY MONT2_STACK (BN_to_montgomery (tree_ops bptr)) false.
  Proof.
    eapply (W_mont.BN_to_montgomery_walk MONT_CS); [cle| | | | | |].
    - intros until qc. intros PRE1. apw W_ctx.BN_CTX_start_walk. eapply bn_pre_wk; [exact PRE1| cle].
    - intros until qc. intros PRE1. apw W_ctx_get.BN_CTX_get_walk. eapply bn_pre_wk; [exact PRE1| cle].
    - intros until qc. intros PRE1. apw W_ctx_end.BN_CTX_end_walk. eapply bn_pre_wk; [exact PRE1| cle].
    - intros until qc. intros PRE1. eapply (W_sqr.bn_sqr_fixed_top_walk_cs HM HF MONT_CS); [cle| exact PRE1].
    - intros until qc. intros PRE1. eapply (W_mul.bn_mul_fixed_top_walk_cs HM HF MONT_CS); [cle| exact PRE1].
    - intros until qm. intros PRE1. eapply (W_from_mont.bn_from_montgomery_word_walk HM HF). eapply bn_pre_wk; [exact PRE1| cle].
  Qed.

  Lemma BN_from_montgomery_closed : W_mont.mont2_stmt W_mont.BN_FROM_MONTGOMERY MONT2_STACK (BN_from_montgomery (tree_ops bptr)) true.
  Proof.
    eapply (W_mont.BN_from_montgomery_walk MONT_CS); [cle| | | | |].
    - intros until qc. intros PRE1. apw W_ctx.BN_CTX_start_walk. eapply bn_pre_wk; [exact PRE1| cle].
    - intros until qc. intros PRE1. apw W_ctx_get.BN_CTX_get_walk. eapply bn_pre_wk; [exact PRE1| cle].
    - intros until qc. intros PRE1. apw W_ctx_end.BN_CTX_end_walk. eapply bn_pre_wk; [exact PRE1| cle].
    - intros until ay. intros PRE1. apw W_copy.BN_copy_walk. eapply bn_pre_wk; [exact PRE1| cle].
    - intros until qm. intros PRE1. eapply (W_from_mont.bn_from_montgomery_word_walk HM HF). eapply bn_pre_wk; [exact PRE1| cle].
  Qed.

  Definition MONTSET_STACK : Z := 17408.
  Definition MONTSET_CS : Z := InvClosed.INV_STACK.
  Lemma BN_MONT_CTX_set_closed : forall (CS : Z), MONTSET_STACK <= CS -> forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BgBnU.BnRep.err_addrs)
      (lo B : Z) (errv : word) (rd : bnref) (ad am ac : Z) (qm qc : bptr),
    bn_pre s bs m OW LB PL EA sp lo B errv CS -> tp = wz RATP -> bv_unsigned sp mod 16 = 0 ->
    ref_at bs OW PL rd ad -> rd <> ROne -> pl_mont PL = Some (am, qm) -> pl_ctx PL = Some (ac, qc) -> pl_bn PL RTmod = None ->
    a0 = wz am -> a1 = wz ad -> a2 = wz ac ->
    implM bgusegs (interp (embed (BN_MONT_CTX_set (tree_ops bptr) rd bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz W_exp_mont.BN_MONT_CTX_SET) fc None m (seg_rom bgusegs)).
  Proof.
    intros CS HCS. intros until qc. intros PRE.
    eapply (W_mont_set.BN_MONT_CTX_set_walk HM HF MONTSET_CS); [cle| cle| cle| cle| cle| cle| cle| cle| cle| cle| cle|].
    eapply bn_pre_wk; [exact PRE|]. revert HCS. unfold MONTSET_STACK, W_mont_set_b.BN_MONT_CTX_SET_STACK, MONTSET_CS. rewrite InvClosed.INV_STACK_val. clear. lia.
  Qed.

  Definition EXPMONT_CS : Z := MONTSET_STACK.
  Definition MONT_STACK : Z := 400 + EXPMONT_CS.
  Definition MONTW_STACK : Z := 128 + EXPMONT_CS.

  Lemma BN_mod_exp_mont_closed : exp_stmt_f BN_MOD_EXP_MONT MONT_STACK (BN_mod_exp_mont (tree_ops bptr)) (Some (wz 0)).
  Proof.
    eapply (W_exp_mont_g.BN_mod_exp_mont_walk EXPMONT_CS); [cle| cle| exact HM| exact HF| cle| cle| | | | | | | | | |].
    - intros until qc. intros PRE1. apw W_ctx.BN_CTX_start_walk. eapply bn_pre_wk; [exact PRE1| cle].
    - intros until qc. intros PRE1. apw W_ctx_get.BN_CTX_get_walk. eapply bn_pre_wk; [exact PRE1| cle].
    - intros until qc. intros PRE1. apw W_ctx_end.BN_CTX_end_walk. eapply bn_pre_wk; [exact PRE1| cle].
    - eapply mont3_wk; [exact bn_mul_mont_fixed_top_closed| cle].
    - eapply mont2_wk; [exact bn_to_mont_fixed_top_closed| cle].
    - eapply mont2_wk; [exact BN_from_montgomery_closed| cle].
    - eapply (BN_MONT_CTX_set_closed EXPMONT_CS). cle.
    - intros until b. intros PRE1. apw W_cmp.BN_ucmp_walk. eapply bn_pre_wk; [exact PRE1| cle].
    - eapply (BN_nnmod_closed EXPMONT_CS). cle.
    - intros until w. intros PRE1 T1 H1 W1 R1 E0 E1.
      first [eapply (W_set_word.BN_set_word_walk HM HF) | eapply (W_set_word.BN_set_word_walk HM)]; [eapply bn_pre_wk; [exact PRE1| cle]| exact T1| exact H1| exact W1| exact E0| exact E1| exact R1].
  Qed.

  Lemma BN_mod_exp_mont_word_closed : forall (CS : Z), MONTW_STACK <= CS -> forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BgBnU.BnRep.err_addrs)
      (lo B : Z) (errv : word) (rr rp rm : bnref) (A : Z) (arr arp arm ac : Z) (qc : bptr),
    bn_pre s bs m OW LB PL EA sp lo B errv CS -> tp = wz RATP -> bv_unsigned sp mod 16 = 0 ->
    ref_at bs OW PL rr arr -> ref_at bs OW PL rp arp -> ref_at bs OW PL rm arm ->
    hpl PL rr -> rp <> ROne -> rm <> ROne -> pl_ctx PL = Some (ac, qc) -> pl_fresh PL -> 0 <= A < BW ->
    a0 = wz arr -> a1 = wz A -> a2 = wz arp -> a3 = wz arm -> a4 = wz ac -> a5 = wz 0 ->
    implM bgusegs (interp (embed (BN_mod_exp_mont_word (tree_ops bptr) rr A rp rm bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (fun _ bs' OW' PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_MOD_EXP_MONT_WORD) fc None m (seg_rom bgusegs)).
  Proof.
    intros CS HCS. intros until qc. intros PRE.
    eapply (W_exp_mont_word.BN_mod_exp_mont_word_walk EXPMONT_CS); [cle| cle| cle| exact HM| exact HF| | | | | | | | | | | exact (bn_pre_wk _ _ _ _ _ _ _ _ _ _ _ _ _ PRE HCS)].
    - intros until qc0. intros PRE1. apw W_ctx.BN_CTX_start_walk. eapply bn_pre_wk; [exact PRE1| cle].
    - intros until qc0. intros PRE1. apw W_ctx_get.BN_CTX_get_walk. eapply bn_pre_wk; [exact PRE1| cle].
    - intros until qc0. intros PRE1. apw W_ctx_end.BN_CTX_end_walk. eapply bn_pre_wk; [exact PRE1| cle].
    - eapply mont3_wk; [exact BN_mod_mul_montgomery_closed| cle].
    - eapply mont2_wk; [exact BN_to_montgomery_closed| cle].
    - eapply mont2_wk; [exact BN_from_montgomery_closed| cle].
    - eapply (BN_MONT_CTX_set_closed EXPMONT_CS). cle.
    - intros until w. intros PRE1 T1 H1 W1 R1 E0 E1.
      first [eapply (W_set_word.BN_set_word_walk HM HF) | eapply (W_set_word.BN_set_word_walk HM)]; [eapply bn_pre_wk; [exact PRE1| cle]| exact T1| exact H1| exact W1| exact E0| exact E1| exact R1].
    - intros until w. intros PRE1. apw W_mul_word.BN_mul_word_walk. eapply bn_pre_wk; [exact PRE1| cle].
    -
      intros until qc0. intros PRE1 -> HA1 HA2 HA3 HP1 N2 N3 HC1 -> -> -> -> ->.
      eapply (W_bndiv.BN_div_walk HM HF) with (dv := None) (rm := Some rr0);
        [eapply bn_pre_wk; [exact PRE1| cle]| reflexivity| exact HC1| reflexivity| exact HA1| exact HA2| exact HA3| intros d X; discriminate X| intros r X; injection X as <-; exact HP1| exact N2| exact N3
        | reflexivity| reflexivity| reflexivity| reflexivity| reflexivity].
  Qed.

  Definition EXP_CS : Z := MONT_STACK.
  Definition MEXP_STACK : Z := 64 + EXP_CS.

  Lemma BN_mod_exp_closed : exp_stmt_f BN_MOD_EXP MEXP_STACK (BN_mod_exp (tree_ops bptr)) None.
  Proof.
    eapply (W_mod_exp.BN_mod_exp_walk EXP_CS); [cle| | |].
    - eapply exp_stmt_f_wk; [exact BN_mod_exp_recp_closed| cle].
    - eapply exp_stmt_f_wk; [exact BN_mod_exp_mont_closed| cle].
    - eapply (BN_mod_exp_mont_word_closed EXP_CS). cle.
  Qed.

End Closed.
End WithCeiling0.
