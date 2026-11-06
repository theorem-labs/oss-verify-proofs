(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.paintcmap_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.O21 Require Import O21LeptStderr O21LeptBase.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.O21 Require Import O21CL7a.
Import O21CL7a.O21LeptErr.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.O21 Require Import O21CL8a.
Import O21CL8a.O21LeptCmap.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.O21 Require Import O21CL9a.
Import O21CL9a.O21LeptCmapDeser.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.O21 Require Import O21CL3a.
Import O21CL3a.O21MaxIndex.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Leptonica Require Import LeptRoom.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common Require LiaFast.   (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Reloc Require Import Reloc.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Leptonica Require Import RelocLept.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Leptonica.OL Require LeptCmapValid.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.O21 Require Import O21Kit.
Import O21Kit.O21Reloc. Import O21Kit.O21RelocCode. Import O21Kit.O21RelocSites. Import O21Kit.O21RelocImg. Import O21Kit.O21RelocOL.
Import O21Kit.O21RelocMusl. Import O21Kit.O21LeptEnv.
Import O21CL7a.O21LeptG.
Import ListNotations.
Open Scope bv_scope.

Section CmapValid.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LL21} {P16 : O21Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
Definition cmap_ok (cv : cmapv) : Prop :=
  (c_d cv = 1 \/ c_d cv = 2 \/ c_d cv = 4 \/ c_d cv = 8)%Z /\ c_nalloc cv = (2 ^ c_d cv)%Z /\ (1 <= c_n cv <= c_nalloc cv)%Z /\ (1 <= c_arr cv)%Z.
Definition pv_post (C : lctx) (A : AS) (s : Z) (m m' : word -> option byte) (pv valid : Z) : Prop :=
  POSTM C A s (wbytes m (Z_to_bv 64 pv) (word_to_le_bytes 4 (Z_to_bv 64 valid))) m'.
Theorem pixcmapIsValid_null_W : forall C A m md regs (s cm pv : Z) (cv : cmapv) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 48 <= s)%Z -> (s <= pv)%Z -> (pv + 4 <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = Z_to_bv 64 cm -> getr regs 11 = Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 pv ->
  CMAPat m cm cv -> cmap_ok cv -> live A (Z_to_bv 64 cm) = Some 24%Z ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> pv_post C A s m m' pv 1 -> getr regs' 10 = Z_to_bv 64 0 ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (0x1564c : word) m al_rom) md) S.
Proof. rl_tail (@LeptCmapValid.pixcmapIsValid_null_W fx o21_reloc o21_code_ol o21_lept AL CL ASR PINS (o21_pinsG P16)). Qed.

Theorem pixcmapIsValid_pix_W : forall C A m md regs (s cm pix pv : Z) (cv : cmapv) (v : pixv) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 48 + LSF <= s)%Z -> (s <= pv)%Z -> (pv + 4 <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = Z_to_bv 64 cm -> getr regs 11 = Z_to_bv 64 pix -> getr regs 12 = Z_to_bv 64 pv ->
  CMAPat m cm cv -> cmap_ok cv -> live A (Z_to_bv 64 cm) = Some 24%Z ->
  PIXat m pix v -> live A (Z_to_bv 64 pix) = Some 64%Z ->
  dval (p_d v) -> (1 <= p_w v <= 20000)%Z -> (1 <= p_h v <= 20000)%Z -> p_wpl v = wpl_of (p_w v) (p_d v) ->
  live A (Z_to_bv 64 (p_data v)) = Some (4 * (p_wpl v * p_h v))%Z ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' ->
     (exists valid, (valid = 0 \/ valid = 1)%Z /\ pv_post C A s m m' pv valid /\ getr regs' 10 = Z_to_bv 64 (1 - valid)) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (0x1564c : word) m al_rom) md) S.
Proof. rl_tail (@LeptCmapValid.pixcmapIsValid_pix_W fx o21_reloc o21_code o21_sites o21_code_ol o21_sites_ol o21_lept o21_img_ol o21_data o21_img o21_rw o21_pf o21_lenv_ol AL CL ASR PINS (o21_pinsG P16)). Qed.

Lemma POSTM_absorb : forall C Ar A M md m2 (s s' : Z) (a : word) bs, Cok C -> W C A M md -> sub_live Ar A ->
  (s' <= s)%Z -> (c_top C - LSTK <= u a)%Z -> (u a + Z.of_nat (length bs) <= s)%Z -> (s <= c_top C)%Z ->
  POSTM C A s' (wbytes M a bs) m2 -> POSTM C Ar s M m2.
Proof. rl_tail (@LeptCmapValid.POSTM_absorb o21_reloc o21_lept AL CL ASR PINS). Qed.

Theorem pixSetColormap_W : forall C Ar A m md regs (s pix cm : Z) (v : pixv) (cv : cmapv) (ret : word) (S : TSet),
  Cok C -> W C A m md -> sub_live Ar A ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 96 <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = Z_to_bv 64 pix -> getr regs 11 = Z_to_bv 64 cm ->
  PIXat m pix v -> p_cmap v = 0%Z ->
  live A (Z_to_bv 64 pix) = Some 64%Z -> live Ar (Z_to_bv 64 pix) = None -> live (c_A0 C) (Z_to_bv 64 pix) = None ->
  CMAPat m cm cv -> cmap_ok cv -> live A (Z_to_bv 64 cm) = Some 24%Z -> Z_to_bv 64 pix <> Z_to_bv 64 cm ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C Ar s m m' ->
      PIXat m' pix (set_cmap v cm) -> CMAPat m' cm cv -> getr regs' 10 = Z_to_bv 64 0 ->
      realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (0x14cc0 : word) m al_rom) md) S.
Proof. rl_tail (@LeptCmapValid.pixSetColormap_W fx o21_reloc o21_code_ol o21_sites_ol o21_lept AL CL ASR PINS (o21_pinsG P16)). Qed.

End CmapValid.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).      (* [comment removed for export] *)
