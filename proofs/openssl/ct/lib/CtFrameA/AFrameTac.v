(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac ZBridge RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Malloc Prog BnBase BnModel BnTree BgState BgInv BgLib.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface D_defs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnW Require Import BnTac BnMem BnTacX.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnP Require Import BnKit BnKit2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import LibKitA ARun BnHeapA ImplA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBgRepA Require ApBnRepA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBgRepA Require Import BgRepDefs BgRep BgLayer BgIface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma land_m32 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551584 = 32 * (x / 32).
Proof.
  intros x Hx. replace (32 * (x / 32)) with (Z.shiftl (Z.shiftr x 5) 5) by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; change (2^5) with 32; lia).
  rewrite <- Z.ldiff_ones_r by lia.
  assert (E : x = Z.land x (Z.ones 64)) by (rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; lia).
  rewrite E at 2. change 18446744073709551584 with (Z.ldiff (Z.ones 64) (Z.ones 5)).
  apply Z.bits_inj'. intros n Hn. rewrite !Z.land_spec, !Z.ldiff_spec, !Z.land_spec.
  destruct (Z.testbit x n), (Z.testbit (Z.ones 64) n), (Z.testbit (Z.ones 5) n); reflexivity.
Qed.

(* [comment removed for export] *)
Lemma realign32 : forall sp F, 0 <= F -> 0 <= sp - F -> sp < 2^64 -> F mod 32 = 0 -> sp mod 16 = 0 ->
  (sp mod 32 = 0 /\ Z.land (sp - F) 18446744073709551584 = sp - F) \/ (sp mod 32 = 16 /\ Z.land (sp - F) 18446744073709551584 = sp - F - 16).
Proof.
  intros sp F HF0 H0 H1 HF H16. rewrite land_m32 by lia.
  assert (C : sp mod 32 = 0 \/ sp mod 32 = 16) by (Z.div_mod_to_equations; lia).
  destruct C as [C|C]; [left | right]; (split; [exact C|]); Z.div_mod_to_equations; lia.
Qed.

Lemma le1_lit : forall (w : word) (b : byte), bv_unsigned w mod 256 = bv_unsigned b -> le1 w = le1 (zxb b).
Proof.
  intros w b H. rewrite le1_zxb. unfold le1. cbn [Z_to_le_bytes]. f_equal. apply bv_eq.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. exact H.
Qed.

(* [comment removed for export] *)
Ltac sbstep :=
  step;
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?w)) _) =>
      let bz := eval vm_compute in (bv_unsigned w mod 256) in
      rewrite (le1_lit w (Z_to_bv 8 bz) ltac:(vm_compute; reflexivity));
      mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 0)) _) =>
      change (Z_to_le_bytes 1 0) with (le1 (zxb (Z_to_bv 8 0)));
      mem_after_store
  | |- _ => idtac
  end.

Section Post.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Definition bn_postAX {A : Type} (XX : list (Z * Z)) (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (Σ : rts RT) (st : ST) (OW LB : list block) (lo : Z) (m : mem) (PL : placement) (EA : ApBnRepA.err_addrs) (cost : Z)
    (RES : A -> ST -> list block -> placement -> word -> mem -> Prop)
    (r : A * ST) (Σ' : rts RT) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m' OW' PL',
    ms' = MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom ctasegs)
    /\ AHEAP Σ' OW' LB m' /\ lib_state (snd r) m' OW' PL' EA
    /\ stk ctasegs m' lo (bv_unsigned sp) /\ mem_inv ctasegs m'
    /\ ax_pres LB (bv_unsigned sp) (XW PL ++ XX) m m'
    /\ rt_credit RT Σ - cost <= rt_credit RT Σ'
    /\ cnt_eq st OW (snd r) OW'
    /\ refs_stable st OW (snd r) OW'
    /\ RES (fst r) (snd r) OW' PL' a0 m'.

Lemma bn_postA_X : forall {A : Type} ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ st OW LB lo m PL EA cost
    (RES : A -> ST -> list block -> placement -> word -> Prop) r Σ' ms,
  bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ st OW LB lo m PL EA cost RES r Σ' ms ->
  bn_postAX [] ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ st OW LB lo m PL EA cost (fun a s o p w _ => RES a s o p w) r Σ' ms.
Proof.
  intros until ms. intros (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & F2 & fc2 & m2 & OW2 & PL2 & E & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
  exists y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, F2, fc2, m2, OW2, PL2.
  rewrite app_nil_r. auto 12.
Qed.

Lemma bn_postAX_A : forall {A : Type} ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ st OW LB lo m PL EA cost
    (RES : A -> ST -> list block -> placement -> word -> Prop) r Σ' ms,
  bn_postAX [] ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ st OW LB lo m PL EA cost (fun a s o p w _ => RES a s o p w) r Σ' ms ->
  bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ st OW LB lo m PL EA cost RES r Σ' ms.
Proof.
  intros until ms. intros (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & F2 & fc2 & m2 & OW2 & PL2 & E & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
  exists y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, F2, fc2, m2, OW2, PL2.
  rewrite app_nil_r in H5. auto 12.
Qed.

End Post.
