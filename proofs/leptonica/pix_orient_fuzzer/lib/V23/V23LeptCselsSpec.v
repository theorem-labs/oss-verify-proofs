(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk FPSteps.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import WalksLib LeptDefs LeptStructs LeptArith LeptExecB LeptRecs LeptSel.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptRoomPC LeptRoom14 LeptRoomBL.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require O23LeptCloseIface O23LeptCselsSpec.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptBase V23LeptDilW V23LeptCloseIface.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CselsSpec.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Definition selectComposableSels_lit_contract : Prop :=
  forall (fr : bvmap 5 word) (cs : bv 32) C A m md regs (s size dir : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md -> frm_zero cs ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + CSELS_STACK <= s)%Z -> (s + 48 <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x1381d0 ->
  getr regs 10 = Z_to_bv 64 size -> getr regs 11 = Z_to_bv 64 dir ->
  getr regs 12 = Z_to_bv 64 (s + O23LeptCselsSpec.csels_k1 size) -> getr regs 13 = Z_to_bv 64 (s + O23LeptCselsSpec.csels_k2 size) ->
  ((size = 8 /\ dir = 2) \/ (size = 30 /\ dir = 1))%Z ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (O23LeptCloseIface.csels_K size <= kR)%Z -> (O23LeptCloseIface.csels_K size * 2 ^ 17 <= bR)%Z ->
  (forall (fr' : bvmap 5 word) (cs' : bv 32) A' m' vm' regs' (sel1 sel2 : Z) (sv1 sv2 : selv) (c1 c2 : Z -> Z -> Z),
     frm_zero cs' -> (forall r : reg, In (u r) fs_list -> reg_get fr' r = reg_get fr r) ->
     W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> getr regs' 10 = Z_to_bv 64 0 ->
     sub_live A A' -> POSTM C A (s + 48) m m' ->
     rdn SEGS m' (Z_to_bv 64 (s + O23LeptCselsSpec.csels_k1 size)) 8 = Some (Z_to_le_bytes 8 sel1) ->
     rdn SEGS m' (Z_to_bv 64 (s + O23LeptCselsSpec.csels_k2 size)) 8 = Some (Z_to_le_bytes 8 sel2) ->
     (forall a : word, (s <= u a < s + 48)%Z -> ~ (s + O23LeptCselsSpec.csels_k1 size <= u a < s + O23LeptCselsSpec.csels_k1 size + 8)%Z ->
                       ~ (s + O23LeptCselsSpec.csels_k2 size <= u a < s + O23LeptCselsSpec.csels_k2 size + 8)%Z -> m' a = m a) ->
     sel_at (alloc_top (c_vm C)) A' m' sel1 sv1 -> sel_at (alloc_top (c_vm C)) A' m' sel2 sv2 ->
     sel_cont m' sv1 c1 -> sel_cont m' sv2 c2 -> v_name sv1 = 0%Z -> v_name sv2 = 0%Z -> O23LeptCloseIface.csels_shape size dir sv1 sv2 ->
     (forall p, sel_blk sel1 sv1 p \/ sel_blk sel2 sv2 p -> live A (Z_to_bv 64 p) = None /\ live (c_A0 C) (Z_to_bv 64 p) = None) ->
     (forall p q, sel_blk sel1 sv1 p -> sel_blk sel2 sv2 q -> p <> q) ->
     (forall q : word, (forall p, sel_blk sel1 sv1 p \/ sel_blk sel2 sv2 p -> q <> Z_to_bv 64 p) -> live A' q = live A q) ->
     aroom A' vm' (kR - O23LeptCloseIface.csels_K size) (bR - O23LeptCloseIface.csels_K size * 2 ^ 17) ->
     realizes SEGS (mkCfg (@mkst (mkFP fr' cs') regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst (mkFP fr cs) regs (0xa3574 : word) m al_rom) md) S.

End CselsSpec.
