(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require StackLayout.
From LinuxProcessSemantics.LinuxProcessSem Require Fs.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Monad.
From LinuxProcessSemantics.LinuxProcessSem Require Specs.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From OSSVerify.leptonica.pix1_fuzzer.images Require Ubsan.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common Require PropExec.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common Require CatExec.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common Require CatSim.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common Require StepTac.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common Require Hoare.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common Require ShapeAlg.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common Require AllocIface.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common Require PureModel.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common Require VmLedger.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common Require StoreOk.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common Require MemSplit.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common Require RefMemcpyLib.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common Require StartupTac.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common Require WalkTac.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Mallocng Require AllocBase.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Mallocng Require AllocCalloc.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Mallocng Require AllocSure.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Leptonica Require SumWalkTac.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Leptonica Require SumSpecs.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Leptonica Require WalksLib.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Leptonica Require W2Lib.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Leptonica Require LibAtomic.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Leptonica Require LeptDefs.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Leptonica Require LeptStructs.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Leptonica Require LeptArith.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.V22 Require V22LeptStderr.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.V22 Require V22LeptBase.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.V22 Require V22CL7a.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.V22 Require V22CL8a.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.V22 Require V22CL3a.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Leptonica Require LeptRoom.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common Require LiaFast.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Reloc Require Reloc.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Leptonica Require RelocLept.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Leptonica.VL Require LeptCmapDeser.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.V22 Require V22Kit.
Module V22LeptCmapDeser.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.Fs.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Monad.
Import LinuxProcessSemantics.LinuxProcessSem.Specs.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.Riscv.Decode.
Import LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.leptonica.pix1_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.StepTac.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.AllocIface.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.PureModel.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.VmLedger.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.StoreOk.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.MemSplit.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.RefMemcpyLib.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.StartupTac.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.WalkTac.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Mallocng.AllocBase.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Mallocng.AllocSure.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Leptonica.SumWalkTac.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Leptonica.SumSpecs.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Leptonica.WalksLib.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Leptonica.W2Lib.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Leptonica.LibAtomic.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Leptonica.LeptDefs.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Leptonica.LeptStructs.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Leptonica.LeptArith.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.V22.V22LeptStderr.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.V22.V22LeptBase.
Import V22CL7a.
Import V22CL8a.
Import V22CL3a.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Leptonica.LeptRoom.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Reloc.Reloc.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Leptonica.RelocLept.
Import V22Kit.
(* [comment removed for export] *)










Import V22CL7a.V22LeptErr.

Import V22CL8a.V22LeptCmap.

Import V22CL3a.V22CmapFill.


Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].




Import V22Kit.V22Reloc. Import V22Kit.V22RelocCode. Import V22Kit.V22RelocSites. Import V22Kit.V22RelocImg. Import V22Kit.V22RelocVL.
Import V22Kit.V22RelocMusl. Import V22Kit.V22LeptEnv.
Import V22CL7a.V22LeptG.
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
Context {PINS : @LeptPins AL LLU22} {P16 : V22Pins}.
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
Proof. rl_tail (@LeptCmapDeser.blk_rdn v22_reloc v22_lept AL CL ASR PINS). Qed.

Theorem pixcmapDeserialize_W : forall C A m md regs (s dp nc : Z) (pb : word) (kb : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 160 + LSF <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x30210 ->
  getr regs 10 = Z_to_bv 64 dp -> getr regs 11 = Z_to_bv 64 4 -> getr regs 12 = Z_to_bv 64 nc -> (1 <= nc <= 256)%Z ->
  live (c_A0 C) pb = Some kb -> (u pb <= dp)%Z -> (dp + 4 * nc <= u pb + kb)%Z ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_cmap <= kR)%Z -> (RB_cmap <= bR)%Z ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     ((getr regs' 10 = Z_to_bv 64 0 /\ forall q, live A' q = live A q)
      \/ (exists cm arr, getr regs' 10 = Z_to_bv 64 cm /\ cmapd_new C A A' m' cm arr nc)) ->
     aroom A' vm' (kR - RK_cmap) (bR - RB_cmap) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x14a5c : word) m al_rom) md) S.
Proof. rl_tail (@LeptCmapDeser.pixcmapDeserialize_W fx v22_reloc v22_code_vl v22_sites_vl v22_lept v22_img_vl v22_data v22_rw AL CL ASR PINS (v22_pinsG P16)). Qed.

End CmapDeser.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).      (* [comment removed for export] *)
End V22LeptCmapDeser.

From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Leptonica Require LeptArith2.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Leptonica.VL Require LeptPixCreate.
Module V22LeptPixCreate.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.Fs.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Monad.
Import LinuxProcessSemantics.LinuxProcessSem.Specs.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.Riscv.Decode.
Import LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.leptonica.pix1_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.StepTac.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.AllocIface.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.PureModel.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.VmLedger.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.StoreOk.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.MemSplit.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.RefMemcpyLib.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.StartupTac.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.WalkTac.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Mallocng.AllocBase.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Mallocng.AllocSure.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Leptonica.SumWalkTac.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Leptonica.SumSpecs.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Leptonica.WalksLib.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Leptonica.W2Lib.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Leptonica.LibAtomic.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Leptonica.LeptDefs.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Leptonica.LeptStructs.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Leptonica.LeptArith.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Leptonica.LeptArith2.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.V22.V22LeptStderr.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.V22.V22LeptBase.
Import V22CL7a.
Import V22CL8a.
Import V22Kit.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Leptonica.LeptRoom.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Reloc.Reloc.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Leptonica.RelocLept.
(* [comment removed for export] *)










Import V22CL7a.V22LeptErr.

Import V22CL8a.V22LeptPixHdr. Import V22CL8a.V22LeptPadBitsW.

Import V22Kit.V22Memset.




Import V22Kit.V22Reloc. Import V22Kit.V22RelocCode. Import V22Kit.V22RelocSites. Import V22Kit.V22RelocImg. Import V22Kit.V22RelocVL.
Import V22Kit.V22RelocMusl. Import V22Kit.V22LeptEnv.
Import V22CL7a.V22LeptG.
Import ListNotations.
Open Scope bv_scope.

Section PixCreate.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU22} {P16 : V22Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
Lemma str_msg_pixd : str16 0x103c3 13.
Proof. rl_tail (@LeptPixCreate.str_msg_pixd v22_reloc v22_img_vl). Qed.

Definition pixr_new (C : lctx) (A A' : AS) (m' : word -> option byte) (pix data : Z) (v : pixv) : Prop :=
  (4096 <= pix)%Z /\ (pix + 64 <= alloc_top (c_vm C))%Z /\ (pix mod 16 = 0)%Z /\
  (4096 <= data)%Z /\ (data + 4 * (p_wpl v * p_h v) <= alloc_top (c_vm C))%Z /\ (data mod 16 = 0)%Z /\ pix <> data /\
  live A (Z_to_bv 64 pix) = None /\ live A (Z_to_bv 64 data) = None /\
  live (c_A0 C) (Z_to_bv 64 pix) = None /\ live (c_A0 C) (Z_to_bv 64 data) = None /\
  live A' (Z_to_bv 64 pix) = Some 64%Z /\ live A' (Z_to_bv 64 data) = Some (4 * (p_wpl v * p_h v))%Z /\
  (forall q, q <> Z_to_bv 64 pix -> q <> Z_to_bv 64 data -> live A' q = live A q) /\
  PIXat m' pix v /\ p_data v = data.
Theorem pixCreateNoInit_W : forall C A m md regs (s w h d : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 96 + LSF <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x30210 ->
  getr regs 10 = Z_to_bv 64 w -> getr regs 11 = Z_to_bv 64 h -> getr regs 12 = Z_to_bv 64 d ->
  (1 <= w <= 1000000)%Z -> (1 <= h <= 1000000)%Z -> (w * h <= 400000000)%Z -> (0 <= d < 2 ^ 64)%Z ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     ((getr regs' 10 = Z_to_bv 64 0 /\ forall q, live A' q = live A q)
      \/ (exists pix data, getr regs' 10 = Z_to_bv 64 pix /\ hdr_ok w h d /\ pixr_new C A A' m' pix data (set_data (pix_hdr w h d) data))) ->
     roomtr A (m_vmmaps md) A' vm' RK_pix RB_pix ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x1398c : word) m al_rom) md) S.
Proof. rl_tail (@LeptPixCreate.pixCreateNoInit_W fx v22_reloc v22_code v22_sites v22_code_vl v22_sites_vl v22_lept v22_img_vl v22_data v22_img v22_rw v22_pf v22_lenv_vl AL CL ASR PINS (v22_pinsG P16)). Qed.

Theorem pixCreate_W : forall C A m md regs (s w h d : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 112 + LSF <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x30210 ->
  getr regs 10 = Z_to_bv 64 w -> getr regs 11 = Z_to_bv 64 h -> getr regs 12 = Z_to_bv 64 d ->
  (1 <= w <= 1000000)%Z -> (1 <= h <= 1000000)%Z -> (w * h <= 400000000)%Z -> (0 <= d < 2 ^ 64)%Z ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     ((getr regs' 10 = Z_to_bv 64 0 /\ forall q, live A' q = live A q)
      \/ (exists pix data, getr regs' 10 = Z_to_bv 64 pix /\ hdr_ok w h d /\ pixr_new C A A' m' pix data (set_data (pix_hdr w h d) data))) ->
     roomtr A (m_vmmaps md) A' vm' RK_pix RB_pix ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x138e8 : word) m al_rom) md) S.
Proof. rl_tail (@LeptPixCreate.pixCreate_W fx v22_reloc v22_code v22_sites v22_code_vl v22_sites_vl v22_lept v22_img_vl v22_data v22_img v22_rw v22_pf v22_lenv_vl AL CL ASR PINS (v22_pinsG P16)). Qed.

End PixCreate.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).      (* [comment removed for export] *)
End V22LeptPixCreate.

From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Leptonica.VL Require LeptPixDestroy.
Module V22LeptPixDestroy.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.Fs.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Monad.
Import LinuxProcessSemantics.LinuxProcessSem.Specs.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.Riscv.Decode.
Import LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.leptonica.pix1_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.StepTac.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.AllocIface.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.PureModel.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.VmLedger.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.StoreOk.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.MemSplit.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.RefMemcpyLib.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.StartupTac.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.WalkTac.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Mallocng.AllocBase.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Mallocng.AllocSure.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Leptonica.SumWalkTac.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Leptonica.SumSpecs.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Leptonica.WalksLib.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Leptonica.W2Lib.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Leptonica.LibAtomic.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Leptonica.LeptDefs.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Leptonica.LeptStructs.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Leptonica.LeptArith.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.V22.V22LeptStderr.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.V22.V22LeptBase.
Import V22CL7a.
Import V22CL8a.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Leptonica.LeptRoom.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Reloc.Reloc.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Leptonica.RelocLept.
Import V22Kit.
(* [comment removed for export] *)










Import V22CL7a.V22LeptErr.

Import V22CL8a.V22LeptCmap.


Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].




Import V22Kit.V22Reloc. Import V22Kit.V22RelocCode. Import V22Kit.V22RelocSites. Import V22Kit.V22RelocImg. Import V22Kit.V22RelocVL.
Import V22Kit.V22RelocMusl. Import V22Kit.V22LeptEnv.
Import V22CL7a.V22LeptG.
Import ListNotations.
Open Scope bv_scope.

Section PixDestroy.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU22} {P16 : V22Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
Definition pixd_post (A A' : AS) (pix data cm arr : Z) : Prop :=
  live A' (Z_to_bv 64 pix) = None /\
  (data <> 0%Z -> live A' (Z_to_bv 64 data) = None) /\
  (cm <> 0%Z -> live A' (Z_to_bv 64 cm) = None /\ live A' (Z_to_bv 64 arr) = None) /\
  (forall q, q <> Z_to_bv 64 pix -> (data <> 0%Z -> q <> Z_to_bv 64 data) -> (cm <> 0%Z -> q <> Z_to_bv 64 cm /\ q <> Z_to_bv 64 arr) ->
             live A' q = live A q).
Theorem pixDestroy_W : forall C A m md regs (s pp pix cm karr R : Z) (v : pixv) (cv : cmapv) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 64 + ALLOC_STACK <= s)%Z -> (s <= pp)%Z -> (pp + 8 <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x30210 -> (pp mod 8 = 0)%Z ->
  getr regs 10 = Z_to_bv 64 pp -> rdn SEGS m (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 pix) ->
  PIXat m pix v -> p_rc v = 1%Z -> p_text v = 0%Z -> p_cmap v = cm ->
  live A (Z_to_bv 64 pix) = Some 64%Z -> live (c_A0 C) (Z_to_bv 64 pix) = None ->
  (p_data v = 0%Z \/ (live A (Z_to_bv 64 (p_data v)) = Some R /\ live (c_A0 C) (Z_to_bv 64 (p_data v)) = None /\ (0 < R)%Z /\
                      p_data v <> pix /\ (cm <> 0%Z -> p_data v <> cm /\ p_data v <> c_arr cv))) ->
  (cm = 0%Z \/ (CMAPat m cm cv /\ live A (Z_to_bv 64 cm) = Some 24%Z /\ live A (Z_to_bv 64 (c_arr cv)) = Some karr /\
                live (c_A0 C) (Z_to_bv 64 cm) = None /\ live (c_A0 C) (Z_to_bv 64 (c_arr cv)) = None /\
                cm <> c_arr cv /\ cm <> pix /\ c_arr cv <> pix /\ (0 < karr)%Z)) ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' ->
     pixd_post A A' pix (p_data v) cm (c_arr cv) ->
     POSTM C (c_A0 C) (pp + 8) m m' -> rdn SEGS m' (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 0) ->
     roomtr A (m_vmmaps md) A' vm' 0 0 ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x13e44 : word) m al_rom) md) S.
Proof. rl_tail (@LeptPixDestroy.pixDestroy_W fx v22_reloc v22_sites v22_code_vl v22_sites_vl v22_lept v22_img_vl v22_data v22_rw AL CL ASR PINS (v22_pinsG P16)). Qed.

End PixDestroy.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).      (* [comment removed for export] *)
End V22LeptPixDestroy.
