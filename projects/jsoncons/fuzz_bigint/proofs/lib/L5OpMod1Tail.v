(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreSpecs L5DivSpecs L5DivSpecsO
     L5CoreSpecsU L5DivSpecsU L5DivSpecsOU.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module L5OM1TAIL.
Section SCFG_1.
Context {SCFG_P : ScfgP}.

Definition xs_foot_hyp (L : heap_layout) (xs_foot : list L5.range) : Prop :=
  Forall (fun r => hl_img_lo L <= fst r /\ fst r + snd r <= hl_img_hi L) xs_foot.

Definition opmod1_tail (L : heap_layout) (HI : heap_iface) : Prop :=
  forall (XS : Type) (xs_pre : XS -> (word -> option byte) -> Prop) (xs_av : XS -> Z) (xs_foot : list L5.range)
         (e2_landed e3_landed : XS -> list (Z * Z) -> credit -> Z -> (word -> option byte) -> bvmap 5 word -> list (Z * Z) -> credit -> Prop),
    L5DSO.xs_agree_hyp XS xs_pre xs_av -> L5DSO.xs_av_hyp XS xs_pre xs_av -> xs_foot_hyp L xs_foot ->
    L5DSO.e2_chain_hyp L HI XS xs_pre xs_av xs_foot e2_landed -> L5DSO.e3_chain_hyp L HI XS xs_pre xs_av xs_foot e3_landed ->
    L5DS.opmod1_spec L HI XS (L5DSO.xs_preL XS xs_pre xs_av L) xs_foot e2_landed e3_landed.

(* [comment removed for export] *)
Definition opmodf1_tail (L : heap_layout) (HI : heap_iface) : Prop :=
  forall (XS : Type) (xs_pre : XS -> (word -> option byte) -> Prop) (xs_av : XS -> Z) (xs_foot : list L5.range)
         (e2_landed e3_landed : XS -> list (Z * Z) -> credit -> Z -> (word -> option byte) -> bvmap 5 word -> list (Z * Z) -> credit -> Prop),
    L5DSOU.xs_agree_hyp XS xs_pre xs_av -> L5DSOU.xs_av_hyp XS xs_pre xs_av -> xs_foot_hyp L xs_foot ->
    L5DSOU.e2_chain_hyp L HI XS xs_pre xs_av xs_foot e2_landed -> L5DSOU.e3_chain_hyp L HI XS xs_pre xs_av xs_foot e3_landed ->
    L5DSU.opmodf1_spec L HI XS (L5DSOU.xs_preL XS xs_pre xs_av L) xs_foot e2_landed e3_landed.

End SCFG_1.
End L5OM1TAIL.
