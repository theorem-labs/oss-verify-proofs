(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.graymorph_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14 Require Import O14LeptStderr O14LeptBase.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14 Require Import O14CL7a.
Import O14CL7a.O14LeptErr.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14 Require Import O14CL8a.
Import O14CL8a.O14LeptCmap.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14 Require Import O14CL3a.
Import O14CL3a.O14CmapFill.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica Require Import LeptRoom.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require LiaFast.   (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Reloc Require Import Reloc.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica Require Import RelocLept.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica.OL Require LeptCmapDeser.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14 Require Import O14Kit.
Import O14Kit.O14Reloc. Import O14Kit.O14RelocCode. Import O14Kit.O14RelocSites. Import O14Kit.O14RelocImg. Import O14Kit.O14RelocOL.
Import O14Kit.O14RelocMusl. Import O14Kit.O14LeptEnv.
Import O14CL7a.O14LeptG.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition cdepth (nc : Z) : Z := if (16 <? nc)%Z then 8 else if (4 <? nc)%Z then 4 else if (nc <? 3)%Z then 1 else 2.
Lemma cdepth_cases : forall nc, (cdepth nc = 1 \/ cdepth nc = 2 \/ cdepth nc = 4 \/ cdepth nc = 8)%Z.
Proof. rl_tail (@LeptCmapDeser.cdepth_cases). Qed.

Lemma cdepth_fits : forall nc, (1 <= nc <= 256)%Z -> (nc <= 2 ^ cdepth nc)%Z /\ (2 <= 2 ^ cdepth nc <= 256)%Z.
Proof. rl_tail (@LeptCmapDeser.cdepth_fits). Qed.

Section CmapDeser.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LL16} {P16 : O14Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
Definition cmapd_new (C : lctx) (A A' : AS) (m' : word -> option byte) (cm arr nc : Z) : Prop :=
  (1 <= cm)%Z /\ (cm + 24 <= alloc_top (c_vm C))%Z /\ (cm mod 16 = 0)%Z /\
  (1 <= arr)%Z /\ (arr + 4 * 2 ^ cdepth nc <= alloc_top (c_vm C))%Z /\ (arr mod 16 = 0)%Z /\ cm <> arr /\
  live A (Z_to_bv 64 cm) = None /\ live A (Z_to_bv 64 arr) = None /\
  live (c_A0 C) (Z_to_bv 64 cm) = None /\ live (c_A0 C) (Z_to_bv 64 arr) = None /\
  live A' (Z_to_bv 64 cm) = Some 24%Z /\ live A' (Z_to_bv 64 arr) = Some (4 * 2 ^ cdepth nc)%Z /\
  (forall q, q <> Z_to_bv 64 cm -> q <> Z_to_bv 64 arr -> live A' q = live A q) /\
  CMAPat m' cm (CMAPV arr (cdepth nc) (2 ^ cdepth nc) nc 0).
Lemma blk_rdn : forall C A m md (p : word) (n a : Z) (k : nat), Cok C -> W C A m md -> live A p = Some n ->
  (u p <= a)%Z -> (a + Z.of_nat k <= u p + n)%Z -> exists bs, rdn SEGS m (Z_to_bv 64 a) k = Some bs.
Proof. rl_tail (@LeptCmapDeser.blk_rdn o14_reloc o14_lept AL CL ASR PINS). Qed.

Theorem pixcmapDeserialize_W : forall C A m md regs (s dp nc : Z) (pb : word) (kb : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 144 + LSF <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x3be10 ->
  getr regs 10 = Z_to_bv 64 dp -> getr regs 11 = Z_to_bv 64 4 -> getr regs 12 = Z_to_bv 64 nc -> (1 <= nc <= 256)%Z ->
  live (c_A0 C) pb = Some kb -> (u pb <= dp)%Z -> (dp + 4 * nc <= u pb + kb)%Z ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_cmap <= kR)%Z -> (RB_cmap <= bR)%Z ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     ((getr regs' 10 = Z_to_bv 64 0 /\ forall q, live A' q = live A q)
      \/ (exists cm arr, getr regs' 10 = Z_to_bv 64 cm /\ cmapd_new C A A' m' cm arr nc)) ->
     aroom A' vm' (kR - RK_cmap) (bR - RB_cmap) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x196e0 : word) m al_rom) md) S.
Proof. rl_tail (@LeptCmapDeser.pixcmapDeserialize_W fx o14_reloc o14_code_ol o14_sites_ol o14_lept o14_img_ol o14_data o14_rw AL CL ASR PINS (o14_pinsG P16)). Qed.

End CmapDeser.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).      (* [comment removed for export] *)
