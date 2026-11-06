(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA
     L5Defs L5Core L5KnA L5LazyA L5DefsAB0 L5CoreAB0 L5CoreSpecsAB0.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module L5ASB.
Import L5CA. Import L5CSA.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Section SCFG_1.
Context {SCFG_P : ScfgP}.

(* [comment removed for export] *)
Definition stksh (ar : asan_run) (M : word -> option byte) (lo : Z) : Prop := shadow_zero M lo ((Z.max (ar_sptop ar) (ar_stack_top ar) - lo) / 8).

Definition MUL10_SCRB : Z := 112 + (RESIZE_SCR + 16).
Definition ADDD_SCRB : Z := 160 + RESIZE_SCR.

Definition arith_spec_atB (pc SCR : Z) (d : Z) (VAL : list Z -> Z -> Z) (y : Z) (L : asan_layout) (ar : asan_run) (HI : asan_iface) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (o sp r : Z) (b : L5.bigobj) (ws : list Z),
    ri_inv HI LB FF LK cr A M (vml_of model) -> amodel_ok A model -> K [] ->
    getr R 10%bv = Z_to_bv 64 o -> getr R 11%bv = Z_to_bv 64 y -> Z.of_nat (L5.bo_len b) < 2 ^ 23 ->
    (L5.bo_dyn b = true -> Z.of_nat (L5.bo_len b) + 1 <= L5.bo_cap b) ->
    (L5.bo_dyn b = false -> L5.bo_len b = 2%nat -> acredit_ok L cr 64) ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    getr R 2%bv = Z_to_bv 64 sp -> sp mod 32 = 0 -> getr R 4%bv = Z_to_bv 64 (hl_tp L) -> astk ar M sp SCR -> stksh ar M (sp - SCR) ->
    ffr FF LK d -> ffrs FF sp ->
    L5.big_at RSEGS M o b -> L5C.obj_limbs RSEGS M b ws -> L5.bo_neg b = false -> aobj FF o 32 -> shadow_zero M o 4 ->
    (forall cap q, L5.bo_st b = L5.BDyn cap q -> In (q, 8 * cap) LB) ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (g : growth) LB' cr' (LK' : list fframe) (A' : list (Z * Z)),
        arith_post L ar LB FF LK' cr M M' R R' o sp SCR b (VAL ws y) g LB' cr' ->
        model_rt model model' -> incl A A' -> amodel_ok A' model' -> incl LK' LK ->
        ri_inv HI LB' FF LK' cr' A' M' (vml_of model') ->
        srealizes RSEGS SCFG (cfg R' r M' model') K) ->
    srealizes RSEGS SCFG (cfg R pc M model) K.
(* [comment removed for export] *)
Definition mul10_specB := arith_spec_atB MUL10 MUL10_SCRB 4 (fun ws _ => 10 * L5.limbs_val ws) 10.
Definition addd_specB (L : asan_layout) (ar : asan_run) (HI : asan_iface) : Prop :=
  forall d, 0 <= d <= 9 -> arith_spec_atB ADDD ADDD_SCRB 5 (fun ws d => L5.limbs_val ws + d) d L ar HI.
End SCFG_1.
End L5ASB.
