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
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgMallocU Require RF_malloc_spec RF_realloc_spec.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg LibOps ProgG.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import InitMem.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Import Layout Lib_iface Lib_kit Driver_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.HX Require Import HxVal HxMem HxStep HxHook.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgHXU Require Import HxuInit HxuInv HxuMain HxuFinal HxuLaws.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnModel.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require Import BnRep.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section BgInst.
Context {CE__ : Ceiling} {RN__ : RunRnd}.
Variable St : Type.
Variable st0 : St.
Variable one : St -> list Z -> lprog (St * Z).

Definition bignum_ops : list lop := map dec_op OPS.

Definition LM_bg : LibModel := mkLibModel St (init_of_ops bignum_ops st0) one.

Definition lib_inv_bg (ls : St) (m : word -> option byte) (OW : list block) : Prop := bg_init_facts m OW.

Definition LSP_bg : @LibSpec LM_bg := @Build_LibSpec LM_bg hx_pristine lib_inv_bg LIBW_HX 65536.

Lemma bg_init_facts_agree : forall OW m m',
  bg_init_facts m OW -> agree_on (fun a => rin_ivs LIBW_HX a \/ in_block OW a) m m' -> bg_init_facts m' OW.
Proof.
  intros OW m m' (EA & ND & HC & (HS & HM) & HX) AG. exists EA. split; [exact ND|].
  assert (HL : forall a, libw a -> rin_ivs LIBW_HX a \/ in_block OW a) by (intros a Ha; left; exact Ha).
  split; [exact (crypto_statics_agree _ m m' AG HL HC)|].
  split; [split; [exact (err_statics_agree _ m m' AG HL HS)|]| exact (ossl_exit_cells_agree _ m m' AG HL HX)].
  apply (err_mem_agree _ m m' OW OW EA AG HL); [| intros q A n _ H; exact H | exact HM].
  intros x Hx. right. destruct HM as (I1 & I2 & I3 & I4 & _). unfold err_fp in Hx.
  destruct Hx as [Hx|[Hx|[Hx|Hx]]]; [exists (ea_pk EA, ea_MK EA, 72) | exists (ea_ps EA, ea_SA EA, 32) | exists (ea_pn EA, ea_ND EA, 128) | exists (ea_pe EA, ea_ES EA, 904)];
    (split; [assumption | cbn [blk_addr blk_size fst snd]; exact Hx]).
Qed.

Lemma LL_bg : @LibLaws LM_bg LSP_bg.
Proof.
  constructor.
  - exact LIBW_HX_img.
  - cbn. lia.
  - cbn. lia.
  -
    intros m Hnone (T1 & T2). split; [exact Hnone|]. split; [exact T1|].
    eapply rw_cells_recast; [exact T2 | cbn; auto | vm_compute; reflexivity | reflexivity].
  -
    intros m m' (H1 & H2 & H3) AG. split; [|split].
    + intros a Ha Hi Hn. rewrite (proj1 (AG a Ha Hi)). exact (H1 a Ha Hi Hn).
    + eapply rw_cells_agree; [exact AG | exact H2 |]. intros a Ha. cbn [cells_size csize Nat.add Z.of_nat] in Ha. cbn [LIBW LSP_bg rin_ivs LIBW_HX fst snd]. lia.
    + eapply rw_cells_agree; [exact AG | exact H3 |]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. cbn [LIBW LSP_bg rin_ivs LIBW_HX fst snd]. lia.
  -
    intros ls OW m m' HI AG. exact (bg_init_facts_agree OW m m' HI AG).
Qed.

Theorem rinit_bg : @rinit_stmt CE__ RN__ LM_bg LSP_bg.
Proof.
  apply (hx_rinit_bg (LM := LM_bg) (LSP := LSP_bg) RF_malloc_spec.rmalloc_spec RF_realloc_spec.rrealloc_spec (st0 : @LS LM_bg)).
  - reflexivity.
  - reflexivity.
  - cbn. lia.
  - intros m H. exact H.
  - intros m OW H. exact H.
Qed.

End BgInst.
