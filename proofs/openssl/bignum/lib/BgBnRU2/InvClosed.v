(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnModel BnTree BnInv BnBridge BgState BgWords BgInv BgLib BgArith.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Import Layout Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require BnRep.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgRepU Require Import BgRepDefs BgRep BgLayer BgIface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnRU Require W_ctx W_ctx_get W_ctx_end W_copy W_cmp W_uadd W_usub W_bndiv W_add.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnRU2 Require W_set_word W_rshift1 W_shift W_sub.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnEU Require W_nnmod.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnRU2 Require Import InvKit W_mod_inverse.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Section Closed.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Local Tactic Notation "apw" uconstr(L) := first [eapply (L HM HF) | eapply (L HM) | eapply (L HF) | eapply L].
  Local Ltac cle := vm_compute; intros XXc; discriminate XXc.

  Definition NNMOD_CS : Z := W_bndiv.BN_DIV_TOP_STACK.
  Definition NNMOD_STACK : Z := 32 + NNMOD_CS.

  Lemma BN_nnmod_cl : forall (CS : Z), NNMOD_STACK <= CS -> forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BgBnU.BnRep.err_addrs)
      (lo B : Z) (errv : word) (rr rx rm : bnref) (ar ax am ac : Z) (qc : bptr),
    bn_pre s bs m OW LB PL EA sp lo B errv CS -> tp = wz RATP ->
    ref_at bs OW PL rr ar -> ref_at bs OW PL rx ax -> ref_at bs OW PL rm am -> hpl PL rr -> rx <> ROne -> rm <> ROne -> pl_ctx PL = Some (ac, qc) ->
    a0 = wz ar -> a1 = wz ax -> a2 = wz am -> a3 = wz ac ->
    implM bgusegs (interp (embed (BN_nnmod (tree_ops bptr) rr rx rm bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz W_mod_inverse.BN_NNMOD) fc None m (seg_rom bgusegs)).
  Proof.
    intros CS HCS. intros until qc. intros PRE.
    eapply (W_nnmod.BN_nnmod_walk NNMOD_CS); [cle| | | | exact (bn_pre_le _ _ _ _ _ _ _ _ _ _ _ _ _ PRE HCS)].
    - intros until qc0. intros PRE1 -> HA1 HA2 HA3 HP1 N2 N3 HC1 -> -> -> -> ->.
      eapply (W_bndiv.BN_div_walk HM HF) with (dv := None) (rm := Some rr0);
        [exact PRE1| reflexivity| exact HC1| reflexivity| exact HA1| exact HA2| exact HA3| intros d X; discriminate X| intros r X; injection X as <-; exact HP1| exact N2| exact N3
        | reflexivity| reflexivity| reflexivity| reflexivity| reflexivity].
    - intros until Y. intros PRE1.
      apw W_add.BN_add_walk. eapply bn_pre_le; [exact PRE1|]. cle.
    - intros until Y. intros PRE1.
      apw W_sub.BN_sub_walk. eapply bn_pre_le; [exact PRE1|]. cle.
  Qed.

  Definition INV_CS : Z := NNMOD_STACK.
  Definition INV_STACK : Z := W_mod_inverse.BN_MOD_INVERSE_STACK INV_CS.
  Lemma INV_STACK_val : INV_STACK = 16992.
  Proof. vm_compute. reflexivity. Qed.

  Definition BN_mod_inverse_r_closed :=
    W_mod_inverse.BN_mod_inverse_r_walk HM HF INV_CS ltac:(cle) ltac:(cle) ltac:(cle) ltac:(cle) ltac:(cle) ltac:(cle) ltac:(cle) ltac:(cle) ltac:(cle)
      ltac:(cle) ltac:(cle) ltac:(cle) (BN_nnmod_cl INV_CS ltac:(cle)).
  Definition BN_mod_inverse_closed :=
    W_mod_inverse.BN_mod_inverse_walk HM HF INV_CS ltac:(cle) ltac:(cle) ltac:(cle) ltac:(cle) ltac:(cle) ltac:(cle) ltac:(cle) ltac:(cle) ltac:(cle)
      ltac:(cle) ltac:(cle) ltac:(cle) (BN_nnmod_cl INV_CS ltac:(cle)).
End Closed.
End WithCeiling0.
