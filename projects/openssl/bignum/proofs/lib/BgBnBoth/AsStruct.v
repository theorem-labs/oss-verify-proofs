(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac Arr. 
From OSSVerify.Proofs.openssl.bignum.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnModel.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgB Require Import Layout RT_iface.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import AsKit AsLoop.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require Import LibKitA ARun BnHeapA BnRepDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section WithSegs.
Variable segs : list Segment.

Lemma acc_rdX : forall W m m1 a n X ad,
  acc segs m a n -> munch W m m1 -> offshW W -> a mod 8 = 0 ->
  a <= X -> X / 8 * 8 + 8 <= a + n -> 0 <= a -> a + n <= 140737488355328 ->
  ad = wa (shad X) ->
  ov_read_bytes segs m1 ad 1 = Some [z8].
Proof.
  intros W m m1 a n X ad ACC MU OFF AL H1 H2 H0 HT ->.
  assert (Es : shad (X / 8 * 8) = shad X) by (unfold shad; f_equal; clear; Z.div_mod_to_equations; lia).
  rewrite <- Es.
  apply (acc_rd0 segs W m m1 a n (X / 8 * 8) _ ACC MU OFF); [ | | exact H2 | | reflexivity].
  - clear. Z.div_mod_to_equations. lia.
  - clear - AL H1. Z.div_mod_to_equations. lia.
  - clear - AL H1 H2 H0 HT. Z.div_mod_to_equations. lia.
Qed.

End WithSegs.

Section WithRT.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Lemma AH_shb : forall Σ OW LB m, AHEAP Σ OW LB m -> shb_cells bgbsegs 6147864 6945336 m.
Proof.
  intros Σ OW LB m H. destruct (af_client_consts RT AF Σ m (AH_art _ _ _ _ H)) as (C1 & C2 & _).
  split; [exact C1 | exact C2].
Qed.

Lemma AH_acc_in : forall Σ OW LB m b a n, AHEAP Σ OW LB m -> In b (OW ++ LB) ->
  blk_addr b <= a -> a + n <= blk_addr b + blk_size b -> acc bgbsegs m a n.
Proof.
  intros Σ OW LB m b a n H Hin H1 H2. destruct (AH_acc _ _ _ _ b H Hin) as [_ ACC]. exact (acc_sub bgbsegs m _ _ a n ACC H1 H2).
Qed.

End WithRT.

Ltac sh_X ad :=
  lazymatch ad with
  | Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 ?X)) 3 + _)%Z => X
  | Z_to_bv 64 (_ + Z.shiftr (bv_unsigned (Z_to_bv 64 ?X)) 3)%Z => X
  | Z_to_bv 64 (Z.shiftr ?X 3 + _)%Z => X
  | Z_to_bv 64 (_ + Z.shiftr ?X 3)%Z => X
  | Z_to_bv 64 (?X / 8 + _)%Z => X
  | Z_to_bv 64 (shad ?X) => X
  end.

Ltac sh_addr_s :=
  unfold wa, shad; f_equal; rewrite ?unsigned_lit by lia; rewrite ?Z.shiftr_div_pow2 by (clear; lia); change (2 ^ 3)%Z with 8%Z;
  unfold SHB; clear; Z.div_mod_to_equations; lia.

Ltac shl_off := first [ assumption | (cbn [offshW]; unfold SHLO, SHHI; repeat (split; [lia|]); exact I) ].
Ltac shl_gran AL := first [ (clear - AL; Z.div_mod_to_equations; lia) | (Z.div_mod_to_equations; lia) ].

Ltac shl_pose RD :=
  let ad := cur_mem_addr in
  let X := sh_X ad in
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mc _) =>
    first [
      match goal with
      | ACC : acc segs ?mb ?a ?n, MU : munch ?W ?mb mc, AL : (?a mod 8 = 0)%Z |- _ =>
          pose proof (acc_rdX segs W mb mc a n X ad ACC MU ltac:(shl_off) AL ltac:(lia) ltac:(shl_gran AL) ltac:(lia) ltac:(lia)
                              ltac:(sh_addr_s)) as RD
      end
    | fail 1 "shl: no (acc, munch, a mod 8 = 0) triple in the context covers the shadow load of" X ]
  end.
Ltac shl := let RD := fresh "RDsh" in shl_pose RD; step; clear RD.
Ltac zshl := let RD := fresh "RDsh" in shl_pose RD; zstep; clear RD.
