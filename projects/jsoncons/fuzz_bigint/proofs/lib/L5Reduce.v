(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Words.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module L5RED.
Abbreviation RSEGS := Plain.M.loaded_segments.
Section SCFG_1.
Context {SCFG_P : ScfgP}.

Definition REDUCE : Z := 0x215d0.          (* [comment removed for export] *)

(* [comment removed for export] *)
Definition cfg {fx : FPState} (R : bvmap 5 word) (pc : Z) (M : word -> option byte) (model : Model) : config :=
  mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) model.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition reduce_post (M M' : word -> option byte) (o : Z) (b : L5.bigobj) (ws : list Z) (R R' : bvmap 5 word) : Prop :=
  let n' := L5W.rlen ws in
  (* [comment removed for export] *)
  L5.big_at RSEGS M' o (L5.BO (if Nat.eqb n' 0 then Z.land (L5.bo_fb b) 253 else L5.bo_fb b) n' (L5.bo_st b))
  /\ regs_preserved R R' /\ getr R' 10%bv = Z_to_bv 64 o
  /\ L5.frame_but [(o, 16)] M M' /\ mem_grows M M'.
(* [comment removed for export] *)

Definition reduce_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet) (o r : Z) (b : L5.bigobj) (ws : list Z),
    m_halted model = None -> m_vm_lazy model = [] ->
    getr R 10%bv = Z_to_bv 64 o -> getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    L5.big_at RSEGS M o b ->
    o mod 8 = 0 -> 2 ^ 20 <= o -> o + 32 <= 2 ^ 47 -> L5.writable RSEGS M o 16 ->
    (* [comment removed for export] *)
    L5.defined M (L5.bo_data o b) (8 * L5.bo_cap b) ->
    L5.limbs_at RSEGS M (L5.bo_data o b) ws -> length ws = L5.bo_len b -> L5W.words_ok ws ->
    (forall cap q, L5.bo_st b = L5.BDyn cap q -> q + 8 * cap <= o \/ o + 32 <= q) ->
    (forall (fx' : FPState) R' M', reduce_post M M' o b ws R R' -> srealizes RSEGS SCFG (cfg R' r M' model) K) ->
    srealizes RSEGS SCFG (cfg R REDUCE M model) K.
End SCFG_1.


End L5RED.
