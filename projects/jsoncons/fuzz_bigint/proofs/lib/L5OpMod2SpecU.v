(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreSpecsU L5DivSpecsU.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module L5OM2SU.
Import L5CSU. Import L5DSU.
Section SCFG_1.
Context {SCFG_P : ScfgP}.

(* [comment removed for export] *)
Definition opmodf2_bytes (capy : Z) : Z := 32 * capy + 1024.

Section Specs.
Variable L : heap_layout.
Variable HI : heap_iface.

Definition opmodf2_post (LB : list (Z * Z)) (cr : credit) (M M' : word -> option byte) (R R' : bvmap 5 word)
           (S ao fba fdo : Z) (by_ : L5.bigobj) (capy : Z) (LB' : list (Z * Z)) (cr' : credit) : Prop :=
  regs_preserved R R'
  /\ (exists by' wy' LB1, L5.big_at RSEGS M' S by' /\ L5C.obj_limbs RSEGS M' by' wy' /\
        match L5.bo_st by_, L5.bo_st by' with
        | L5.BDyn cap q, L5.BDyn cap' q' => cap' = cap /\ q' = q /\ LB1 = LB /\ L5.defined M' q (8 * cap)
        | L5.BInl _ _, L5.BInl _ _ => LB1 = LB
        | L5.BInl _ _, L5.BDyn cap' q' => cap' = 8 /\ LB1 = (q', 64) :: LB /\ L5C.fresh_block L LB M' q' 64
        | L5.BDyn _ _, L5.BInl _ _ => False
        end /\ c_after L LB1 M' (S + 32) fdo by' wy' LB')
  /\ a_ok M' ao fba
  /\ credit_after L cr OPMOD2_K (opmodf2_bytes capy) cr'
  /\ L5C.hpres L LB S SCR_OPMOD [(S, 64); (L5.bo_data S by_, 8 * L5.bo_cap by_)] M M'.

Definition opmodf2_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (cr : credit) (S ao fba fdo : Z) (by_ : L5.bigobj) (wy : list Z),
    let capy := L5.bo_cap by_ in
    hi_heap HI LB cr M (m_vmmaps model) -> model_ok model -> K [] ->
    getr R 10%bv = Z_to_bv 64 (S + 32) -> getr R 11%bv = Z_to_bv 64 S -> getr R 12%bv = Z_to_bv 64 ao -> ao = S + 160 ->
    getr R 1%bv = Z_to_bv 64 OPMOD2_RET ->
    getr R 2%bv = Z_to_bv 64 S -> getr R 3%bv = Z_to_bv 64 GP -> getr R 4%bv = Z_to_bv 64 TP ->
    L5C.stk (hl_sptop L) M S SCR_OPMOD -> S + 240 <= hl_sptop L -> L5.writable RSEGS M S 64 ->
    (forall cap q, L5.bo_st by_ = L5.BDyn cap q -> L5.writable RSEGS M q (8 * cap)) ->
    L5.img_clear M 0x10000 0x20000 ->
    y_ok LB M S by_ wy -> (1 <= L5.bo_len by_)%nat -> L5.bo_cap by_ <= 268 ->
    L5.u8_at RSEGS M (S + 32) fdo -> 0 <= fdo < 256 ->          (* [comment removed for export] *)
    a_ok M ao fba ->
    credit_for L cr OPMOD2_K (opmodf2_bytes capy) ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) LB' cr',
        opmodf2_post LB cr M M' R R' S ao fba fdo by_ capy LB' cr' ->
        model_but_vm model model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
        srealizes RSEGS SCFG (cfg R' OPMOD2_RET M' model') K) ->
    srealizes RSEGS SCFG (cfg R OPMODF M model) K.

End Specs.
End SCFG_1.
End L5OM2SU.
