(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac Image.
From OSSVerify.Proofs.openssl.bignum.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.openssl.bignum.lib.BgMallocP Require Import RMallocRep RMalloc_iface.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Prog LibProg ProgG.
From OSSVerify.Proofs.openssl.bignum.lib.BgP Require Import Layout Exit_defs Lib_iface Lib_kit Driver_iface.
From OSSVerify.Proofs.openssl.bignum.lib.BgHXP Require Import HxpInit.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.openssl.bignum.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd} {LM : LibModel} {LSP : LibSpec}.

Lemma LIBW_HX_img : forall a, rin_ivs LIBW_HX a -> 0x27b000 <= a < 0x30d000 /\ ~ ralloc_static a /\ ~ drv_addr a.
Proof.
  intros a H. cbn [rin_ivs LIBW_HX fst snd] in H.
  unfold ralloc_static, drv_addr, stdout_addr, stderr_addr, lxs_addr, ssp_addr, exit_statics_addr, LIB_TCB,
    RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP,
    RINIT_FLAG, RGOT_LLVMINIT, LX_GOT_STDERR, LX_STDERR_PTR, got_ssp, ssp_guard.
  cbn [rin_ivs fst snd]. unfold bgpstage. lia.
Qed.

End WithCeiling0.
