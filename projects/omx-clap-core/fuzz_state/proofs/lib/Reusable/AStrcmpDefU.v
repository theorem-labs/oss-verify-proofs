(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the strcmp contract of record (AStrcmpDef.astrcmp_realizes) lifted to user-poisoned heads,
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_grant/lib/AStrcmpDefU.v (donor image sha256 c2c7559b29bd), with its module paths changed. *)
   per a Theorem Labs lane's ruling of 2026-10-29 and the text agreed with libreac/fuzz_state (a Theorem Labs lane,
   (internal path)). Against AStrcmpDef.v's definition there are exactly six token changes:
   the name; the binder U after S; ecall_pre segs B -> ecall_preU and its U; AR segs B -> ARU in the post and its U. Every
   other premise stays over the raw memory, because the interceptor reads the raw shadow and unpoison changes only the
   user-poisoned heads' shadow bytes (UPoison.v). AStrcmpDef.v is unchanged, so its consumers rebuild nothing; at U = [] this
   text is that one (astrcmp_realizes_of_U). The stack window stays the literal 2 * ESTACK of the plain text. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import AStrcmpDef UPoison.
Import ListNotations.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section c.
Variable segs : list Segment.
Variable B : asyms.

Definition astrcmp_realizesU (pc : Z) : Prop :=
  forall ly S (U : list (Z * Z)) W regs mem md x y k c1 c2,
  ecall_preU segs B ly S U W regs mem md ->
  ly_stk_lo ly + 2 * ESTACK <= spZ regs -> (forall a, spZ regs - 2 * ESTACK <= a < spZ regs -> apresent (w_H W) mem a) ->
  getr regs 10 = w64 x -> getr regs 11 = w64 y -> 0 < x -> 0 < y ->
  k + 1 < 2 ^ 32 -> x + k + 1 <= 2 ^ 63 -> y + k + 1 <= 2 ^ 63 ->
  str_meet segs W mem x y k c1 c2 ->
  src_ok segs W regs mem x (k + 1) -> src_ok segs W regs mem y (k + 1) ->
  (forall a, x <= a <= x + k -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) ->
  (forall a, y <= a <= y + k -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) ->
  amem_range x (k + 1) -> amem_range y (k + 1) ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF x (k + 1) -> shadow_hull_vis (aview segs (w_H W) mem) x (k + 1) ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF y (k + 1) -> shadow_hull_vis (aview segs (w_H W) mem) y (k + 1) ->
  SRr segs W (cfg_at segs pc regs mem md)
    (fun W' c' => W' = W /\ exists regs' mem' md',
       c' = cfg_at segs (raZ regs) regs' mem' md' /\
       ARU segs B ly S U W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
       getr regs' 10 = w64 (strcmp_res c1 c2) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs) ->
          aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
       (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).

(* At U = [] the lifted text is the plain one: a proof of the U form gives the contract of record. *)
Lemma astrcmp_realizes_of_U : forall pc, astrcmp_realizesU pc -> astrcmp_realizes segs B pc.
Proof.
intros pc HU ly S W regs mem md x y k c1 c2 Hpre.
specialize (HU ly S [] W regs mem md x y k c1 c2 (proj2 (ecall_preU_nil segs B ly S W regs mem md) Hpre)).
intros H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20.
eapply SRr_mono; [exact (HU H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20)|].
intros W' c' _ (EW & regs' & mem' & md' & Ec & HAR & Hrest). split; [exact EW|].
exists regs', mem', md'. split; [exact Ec|]. split; [exact (proj1 (ARU_nil segs B ly S W mem' md') HAR)|]. exact Hrest.
Qed.
End c.
End b.
(* Donor (provenance of this file, origin first): libreac/fuzz_grant lib/Reusable/AStrcmpDefU.v (file sha256 3376fba9bb13; donor not released), copied, module paths changed. *)
