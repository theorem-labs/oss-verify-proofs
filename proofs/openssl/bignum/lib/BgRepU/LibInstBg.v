(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.
From Stdlib Require Import ZArith List Lia Bool Permutation.
From Stdlib Require Import Uint63.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX Frame.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgMallocU Require Import RMallocRep RMallocTree RMalloc_iface RRealloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg LibOps ProgG.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Import Layout Exit_defs Lib_iface Lib_kit Driver_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgHXU Require Import HxuInit HxuMain HxuFinal HxuLaws HxuInstBg.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnModel BgState.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require Import BnRep.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgRepU Require Import BgRepDefs BgRep BgLayer.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section BgInstR.
Context {CE__ : Ceiling} {RN__ : RunRnd}.
Variable St : Type.
Variable st0 : St.
Variable one : St -> list Z -> lprog (St * Z).

Lemma wa_of_word : forall a : word, wa (bv_unsigned a) = a.
Proof. intros a. unfold wa. apply Z_to_bv_bv_unsigned. Qed.

Definition lib_pristine_bgr (m : word -> option byte) : Prop :=
  hx_pristine m /\ (forall a : word, CONST_ONE <= bv_unsigned a < CONST_ONE + BN_STRUCT_SZ -> m a = None)
  /\ (forall a : word, GOT_BN_ADD <= bv_unsigned a < GOT_BN_ADD + 16 -> m a = None).

Definition lib_inv_bgr' (ls : St) (m : word -> option byte) (OW : list block) : Prop := lib_inv_bgr m OW.

Definition LSP_bgr : @LibSpec (LM_bg St st0 one) := @Build_LibSpec (LM_bg St st0 one) lib_pristine_bgr lib_inv_bgr' LIBW_bgr 65536.

Lemma LIBW_bgr_img : forall a, rin_ivs LIBW_bgr a -> 0x2c0000 <= a < 0x353000 /\ ~ ralloc_static a /\ ~ drv_addr a.
Proof.
  intros a H. unfold LIBW_bgr in H. apply rin_ivs_app in H. destruct H as [H|H]; [exact (LIBW_HX_img a H)|].
  cbn [rin_ivs fst snd] in H. unfold CONST_ONE, BN_STRUCT_SZ in H.
  unfold ralloc_static, drv_addr, stdout_addr, stderr_addr, lxs_addr, ssp_addr, exit_statics_addr, LIB_TCB,
    RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP,
    RINIT_FLAG, RGOT_LLVMINIT, LX_GOT_STDERR, LX_STDERR_PTR, got_ssp, ssp_guard.
  cbn [rin_ivs fst snd]. unfold bgustage. lia.
Qed.

Lemma lib_inv_bgr_agree : forall OW m m',
  lib_inv_bgr m OW -> agree_on (fun a => rin_ivs LIBW_bgr a \/ in_block OW a) m m' -> lib_inv_bgr m' OW.
Proof.
  intros OW m m' (HB & HONE & HGOT) AG. split; [|split].
  - apply (bg_init_facts_agree OW m m' HB). eapply agree_on_mono; [exact AG|]. intros a [Ha|Ha]; [left; apply libw_bn; exact Ha| right; exact Ha].
  - unfold const_one_cells in *. eapply ro_cells_agree; [exact AG| exact HONE|]. intros a Ha. left. apply libw_const_one. cbn in Ha. unfold BN_STRUCT_SZ. lia.
  - eapply got_arith_cells_agree; [exact AG| | exact HGOT]. intros a Ha. left. exact Ha.
Qed.

Lemma LL_bgr : @LibLaws (LM_bg St st0 one) LSP_bgr.
Proof.
  pose proof (LL_bg St st0 one) as [L1 L2 L3 L4 L5 L6].
  constructor.
  - exact LIBW_bgr_img.
  - cbn. lia.
  - cbn. lia.
  -
    intros m Hnone HT. split; [|split].
    + apply L4; [|exact HT]. intros a Ha Hi Hn. apply Hnone; [exact Ha| | exact Hn]. cbn [LIBW LSP_bgr]. unfold LIBW_bgr. apply rin_ivs_app. left. exact Hi.
    + intros a Ha. rewrite <- (wa_of_word a). apply Hnone.
      * pose proof (bv_unsigned_in_range 64 a) as B. unfold bv_modulus in B. change (2 ^ Z.of_N 64) with (2 ^ 64) in B. lia.
      * cbn [LIBW LSP_bgr]. unfold LIBW_bgr. apply rin_ivs_app. right. cbn. lia.
      * unfold LIB_TCB, CONST_ONE, BN_STRUCT_SZ in *. cbn [rin_ivs fst snd]. lia.
    + intros a Ha. rewrite <- (wa_of_word a). apply Hnone.
      * pose proof (bv_unsigned_in_range 64 a) as B. unfold bv_modulus in B. change (2 ^ Z.of_N 64) with (2 ^ 64) in B. lia.
      * cbn [LIBW LSP_bgr]. unfold LIBW_bgr. apply rin_ivs_app. right. unfold GOT_BN_ADD in Ha. cbn. lia.
      * unfold LIB_TCB, GOT_BN_ADD in *. cbn [rin_ivs fst snd]. lia.
  -
    intros m m' (H1 & H2 & H3) AG. split; [|split].
    + eapply L5; [exact H1|]. eapply agree_on_mono; [exact AG|]. intros a Ha. cbn [LIBW LSP_bgr LSP_bg] in *. unfold LIBW_bgr. apply rin_ivs_app. left. exact Ha.
    + intros a Ha. pose proof (bv_unsigned_in_range 64 a) as B. unfold bv_modulus in B. change (2 ^ Z.of_N 64) with (2 ^ 64) in B.
      assert (HL : rin_ivs (@LIBW (LM_bg St st0 one) LSP_bgr) (bv_unsigned a)).
      { cbn [LIBW LSP_bgr]. unfold LIBW_bgr. apply rin_ivs_app. right. cbn. lia. }
      pose proof (proj1 (AG (bv_unsigned a) ltac:(lia) HL)) as E. rewrite wa_of_word in E. rewrite E. exact (H2 a Ha).
    + intros a Ha. pose proof (bv_unsigned_in_range 64 a) as B. unfold bv_modulus in B. change (2 ^ Z.of_N 64) with (2 ^ 64) in B.
      assert (HL : rin_ivs (@LIBW (LM_bg St st0 one) LSP_bgr) (bv_unsigned a)).
      { cbn [LIBW LSP_bgr]. unfold LIBW_bgr. apply rin_ivs_app. right. unfold GOT_BN_ADD in Ha. cbn. lia. }
      pose proof (proj1 (AG (bv_unsigned a) ltac:(lia) HL)) as E. rewrite wa_of_word in E. rewrite E. exact (H3 a Ha).
  -
    intros ls OW m m' HI AG. exact (lib_inv_bgr_agree OW m m' HI AG).
Qed.

Theorem rinit_bgr : @rinit_stmt CE__ RN__ (LM_bg St st0 one) LSP_bgr.
Proof.
  unfold rinit_stmt. intros until canary.
  intros Hheap Hlxs Hstderr Hssp Haux HspB HB63 Hstk Hlo1 Hlo2 Hlo3 Herr Etp Hmi Hsp16 Hfrm (Hprist & Hone & Hgot) Hslot Ea0 Ea1.
  pose proof (rinit_bg St st0 one) as RI. unfold rinit_stmt in RI.
  specialize (RI ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB lo B errv canary
                 Hheap Hlxs Hstderr Hssp Haux HspB HB63 Hstk Hlo1 Hlo2 Hlo3 Herr Etp Hmi Hsp16 Hfrm Hprist Hslot Ea0 Ea1).
  eapply implM_mono; [exact RI|]. intros ls' s' ms' PO. unfold rlib_post in *.
  destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & F' & fc' & m' & OW' & E & ENV & INV & OX & R0 & PM).
  exists y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, F', fc', m', OW'.
  split; [exact E|]. destruct ENV as (ENV1 & FRM & LXP & SO & FA). split.
  { split; [exact ENV1|]. split; [exact FRM|]. split; [|split; assumption].
    eapply lx_pres_weaken; [exact LXP| lia| auto|]. intros a Ha. cbn [LIBW LSP_bgr LSP_bg] in *. unfold LIBW_bgr. apply rin_ivs_app. left. exact Ha. }
  split; [|split; [exact OX| split; [exact R0| exact PM]]].
  cbn [lib_inv LSP_bgr LSP_bg lib_inv_bg] in *. unfold lib_inv_bgr', lib_inv_bgr. split; [exact INV|]. split.
  -
    apply const_one_cells_of_pristine. intros a Ha. rewrite <- (wa_of_word a).
    pose proof (bv_unsigned_in_range 64 a) as BB. unfold bv_modulus in BB. change (2 ^ Z.of_N 64) with (2 ^ 64) in BB.
    assert (HCL : lx_client LB (bv_unsigned sp) (@LIBW (LM_bg St st0 one) (LSP_bg St st0 one)) (bv_unsigned a)).
    { split.
      - cbn [LIBW LSP_bg]. unfold CONST_ONE, BN_STRUCT_SZ in Ha. cbn [rin_ivs LIBW_HX fst snd]. lia.
      - right; right. unfold CONST_ONE, BN_STRUCT_SZ in Ha. unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP. lia. }
    pose proof (proj1 (LXP (bv_unsigned a) ltac:(lia) HCL)) as E2. rewrite E2. rewrite wa_of_word. exact (Hone a Ha).
  -
    apply got_arith_cells_of_pristine. intros a Ha. rewrite <- (wa_of_word a).
    pose proof (bv_unsigned_in_range 64 a) as BB. unfold bv_modulus in BB. change (2 ^ Z.of_N 64) with (2 ^ 64) in BB.
    assert (HCL : lx_client LB (bv_unsigned sp) (@LIBW (LM_bg St st0 one) (LSP_bg St st0 one)) (bv_unsigned a)).
    { split.
      - cbn [LIBW LSP_bg]. unfold GOT_BN_ADD in Ha. cbn [rin_ivs LIBW_HX fst snd]. lia.
      - right; right. unfold GOT_BN_ADD in Ha. unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP. lia. }
    pose proof (proj1 (LXP (bv_unsigned a) ltac:(lia) HCL)) as E2. rewrite E2. rewrite wa_of_word. exact (Hgot a Ha).
Qed.

End BgInstR.
