(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac Arr ImageA.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Spec Require Import BnBase BnModel.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import RT_iface.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnW Require Import BnTac.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnAsan Require Import AsKit AsLoop. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import LibKitA ARun BnHeapA BnRepDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
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

(* [comment removed for export] *)
Lemma shl32_shr32 : forall x, 0 <= x < 2^32 ->
  bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 x)) 32))) 32)) = x.
Proof.
  intros x Hx. rewrite (unsigned_lit x) by lia. rewrite Z.shiftl_mul_pow2 by lia. rewrite (unsigned_lit (x * 2^32)) by lia.
  rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_mul by lia. apply unsigned_lit. lia.
Qed.

Section WithRT.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

(* [comment removed for export] *)
Lemma AH_shb : forall Σ OW LB m, AHEAP Σ OW LB m -> shb_cells bsegs 6163672 6961656 m.
Proof.
  intros Σ OW LB m H. destruct (af_client_consts RT AF Σ m (AH_art _ _ _ _ H)) as (C1 & C2 & _).
  split; [exact C1 | exact C2].
Qed.

(* [comment removed for export] *)
Lemma AH_acc_in : forall Σ OW LB m b a n, AHEAP Σ OW LB m -> In b (OW ++ LB) ->
  blk_addr b <= a -> a + n <= blk_addr b + blk_size b -> acc bsegs m a n.
Proof.
  intros Σ OW LB m b a n H Hin H1 H2. destruct (AH_acc _ _ _ _ b H Hin) as [_ ACC]. exact (acc_sub bsegs m _ _ a n ACC H1 H2).
Qed.

(* [comment removed for export] *)
Lemma ref_at_al8 : forall Σ OW LB m ls AD r a, AHEAP Σ OW LB m -> ad_blocks OW AD -> ref_at ls OW AD r a -> a mod 8 = 0.
Proof.
  intros Σ OW LB m ls AD r a H (B1 & B2 & B3 & B4 & B5 & BC) HA.
  assert (A16 : forall p A n, In (p, A, n) OW -> A mod 8 = 0).
  { intros p A n Hin. pose proof (AH_okA _ _ _ _ _ _ _ H Hin) as [H16 _]. clear - H16. Z.div_mod_to_equations. lia. }
  destruct r as [| | | | |i]; cbn [ref_at] in HA; subst; eauto.
  destruct HA as (p & Hd & _ & Hin & _ & ->). pose proof (A16 _ _ _ Hin) as E. clear - E. Z.div_mod_to_equations. lia.
Qed.

End WithRT.

(* [comment removed for export] *)
Ltac sh_X ad :=
  lazymatch ad with
  | Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 ?X)) 3 + _)%Z => X
  | Z_to_bv 64 (_ + Z.shiftr (bv_unsigned (Z_to_bv 64 ?X)) 3)%Z => X
  | Z_to_bv 64 (Z.shiftr ?X 3 + _)%Z => X
  | Z_to_bv 64 (_ + Z.shiftr ?X 3)%Z => X
  | Z_to_bv 64 (?X / 8 + _)%Z => X
  | Z_to_bv 64 (shad ?X) => X
  end.

(* [comment removed for export] *)
Ltac sh_addr_s :=
  unfold wa, shad; f_equal; rewrite ?unsigned_lit by lia; rewrite ?Z.shiftr_div_pow2 by (clear; lia); change (2 ^ 3)%Z with 8%Z;
  unfold SHB; clear; Z.div_mod_to_equations; lia.

Ltac shl_off := first [ assumption | (cbn [offshW]; unfold SHLO, SHHI; repeat (split; [lia|]); exact I) ].
Ltac shl_gran AL := first [ (clear - AL; Z.div_mod_to_equations; lia) | (Z.div_mod_to_equations; lia) ].

(* [comment removed for export] *)
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
