(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk FPSteps.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import WalksLib LeptDefs LeptStructs LeptArith LeptExecB.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptRoomPC LeptRoom14 LeptRoomBL.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require O23LeptPixHdr O23LeptCloseSpec.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptBase V23LeptMbc.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition CSC_STACK : Z := 112 + 48 + 4192 + 16.

Section CloseSpec.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Definition csc_K (fr : bvmap 5 word) C Ar A m md regs (s pix1 vs w h cm datas : Z) (cv : cmapv) (ret : word) (S : TSet) (kR bR : Z) : Prop :=
  forall (fr' : bvmap 5 word) (cs' : bv 32) A' m' vm' regs' (cm' : Z) (cv' : cmapv),
     frm_zero cs' -> (forall r : reg, In (u r) fs_list -> reg_get fr' r = reg_get fr r) ->
     W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> getr regs' 10 = Z_to_bv 64 pix1 ->
     sub_live Ar A' -> POSTM C Ar s m m' ->
     O23LeptCloseSpec.pix1_at C Ar A' m' pix1 w h cm' datas cv' -> O23LeptCloseSpec.csc_live A A' cm cv cm' cv' ->
     aroom A' vm' (kR - O23LeptCloseSpec.RK_csc vs) (bR - O23LeptCloseSpec.RB_csc vs w h cm) ->
     realizes SEGS (mkCfg (@mkst (mkFP fr' cs') regs' ret m' al_rom) (with_vmmaps vm' md)) S.

Definition pixCloseSafeCompBrick_inplace_contract : Prop :=
  forall (fr : bvmap 5 word) (cs : bv 32) C Ar A m md regs (s pix1 hs vs w h cm datas : Z) (cv : cmapv) (ret : word) (S : TSet),
  Cok C -> MBC C -> W C A m md -> sub_live Ar A -> frm_zero cs ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + CSC_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x1381d0 ->
  getr regs 10 = Z_to_bv 64 pix1 -> getr regs 11 = Z_to_bv 64 pix1 -> getr regs 12 = Z_to_bv 64 hs -> getr regs 13 = Z_to_bv 64 vs ->
  ((hs = 1 /\ vs = 8) \/ (hs = 30 /\ vs = 1))%Z ->
  O23LeptCloseSpec.pix1_at C Ar A m pix1 w h cm datas cv -> pix1 <> datas -> O23LeptPixHdr.hdr_ok w h 1 -> (1 <= w)%Z -> (1 <= h)%Z ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (O23LeptCloseSpec.RK_csc vs <= kR)%Z -> (O23LeptCloseSpec.RB_csc vs w h cm <= bR)%Z ->
  csc_K fr C Ar A m md regs s pix1 vs w h cm datas cv ret S kR bR ->
  realizes SEGS (mkCfg (@mkst (mkFP fr cs) regs (0xa4878 : word) m al_rom) md) S.

End CloseSpec.
