(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg FPInv AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac RegsEquiv Bridge.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require Import HIface.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Section HeapIfaceInit.
  Variable segs : list Segment.
  Variable cfg : SpuriousCfg.
  Variable HS : Type.
  Variable Heap : HS -> (word -> option byte) -> Model -> Prop.
  Variable blocks : HS -> list (Z * Z).
  Variable owned : HS -> list ivl.
  Variables GP TP : word.
  Variable HTOP : Z.
  Variable KEEP : list ivl.
  (* [comment removed for export] *)
  Variable HeapI : HS -> (word -> option byte) -> Model -> Prop.
  Variable INIT : HS -> list ivl.

  (* [comment removed for export] *)
  Definition malloc_contract_init (PCM NEED : Z) : Prop :=
    forall (fx : FPState) regs m md hs (n : Z) (ret : word) (K : TSet),
      HeapI hs m md -> md_ok md -> (U md + MCHARGE n <= UBOUND)%Z ->
      getr regs 10 = Z_to_bv 64 n -> (1 <= n <= 2^26)%Z ->
      getr regs 1 = ret -> (bv_unsigned ret mod 2 = 0)%Z ->
      getr regs 3 = GP -> getr regs 4 = TP ->
      (sp_of regs mod 16 = 0)%Z -> (sp_of regs <= 2^47)%Z -> (HTOP <= sp_of regs - NEED)%Z ->
      stk segs m (sp_of regs - NEED) (sp_of regs) ->
      (forall x : Z, ~ outside (INIT hs) x -> (sp_of regs <= x)%Z) ->
      (forall (fx' : FPState) regs' m' md' hs' (p : Z),
         @fp_csr fx' = @fp_csr fx -> Heap hs' m' md' -> md_ok md' -> vm_only md md' -> (U md' <= U md + MCHARGE n)%Z ->
         (forall a, ~ outside KEEP a -> m' (wa a) = m (wa a)) ->
         getr regs' 10 = Z_to_bv 64 p -> (p mod 16 = 0)%Z ->
         blocks_add (blocks hs) (blocks hs') (p, n) -> ~ In (p, n) (blocks hs) ->
         callee_saved regs regs' ->
         munch (owned hs ++ owned hs' ++ [(p, p + n); (sp_of regs - NEED, sp_of regs)]%Z) m m' ->
         stk segs m' (sp_of regs - NEED) (sp_of regs) ->
         realizes_cfg segs cfg (mkCfg (@mkst fx' regs' ret m' (seg_rom segs)) md') K) ->
      realizes_cfg segs cfg (mkCfg (@mkst fx regs (Z_to_bv 64 PCM) m (seg_rom segs)) md) K.

  (* [comment removed for export] *)
  Definition heap_frame_init : Prop :=
    forall hs m m' md (W : list ivl), HeapI hs m md -> munch W m m' -> wmono segs m m' ->
      (forall x : Z, ~ outside W x -> outside (owned hs) x /\ outside (INIT hs) x) -> HeapI hs m' md.
End HeapIfaceInit.

(* [comment removed for export] *)
Definition heap_init_ok (segs : list Segment) (cfg : SpuriousCfg) (HI : heap_iface)
    (HeapI : hi_HS HI -> (word -> option byte) -> Model -> Prop) (INIT : hi_HS HI -> list ivl)
    (GP TP : word) (HTOP : Z) (KEEP : list ivl) (PCM MNEED : Z) : Prop :=
  malloc_contract_init segs cfg (hi_HS HI) (hi_Heap HI) (hi_blocks HI) (hi_owned HI) GP TP HTOP KEEP HeapI INIT PCM MNEED /\
  heap_frame_init segs (hi_HS HI) (hi_owned HI) HeapI INIT.
