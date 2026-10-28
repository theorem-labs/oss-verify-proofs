(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
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
From OssFuzzTheorems.leptonica.grayquant_fuzzer.images Require Ubsan.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require PropExec.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require CatExec.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require CatSim.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require StepTac.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Hoare.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require ShapeAlg.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require AllocIface.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require PureModel.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require VmLedger.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require StoreOk.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require MemSplit.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require RefMemcpyLib.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require StartupTac.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require WalkTac.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng Require AllocBase.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng Require AllocCalloc.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng Require AllocSure.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require SumWalkTac.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require SumSpecs.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require WalksLib.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require W2Lib.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LibAtomic.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptDefs.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptStructs.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptArith.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15LeptStderr.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15LeptBase.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15CL7a.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15CL8a.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15CL3a.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptRoom.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require LiaFast.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Reloc Require Reloc.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require RelocLept.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.VL Require LeptCmapDeser.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15Kit.
Module V15LeptCmapDeser.
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
Import OssFuzzTheorems.leptonica.grayquant_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CatExec.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CatSim.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.StepTac.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Hoare.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.ShapeAlg.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.AllocIface.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.PureModel.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.VmLedger.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.StoreOk.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.MemSplit.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.RefMemcpyLib.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.StartupTac.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.WalkTac.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocBase.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocSure.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.SumWalkTac.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.SumSpecs.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.WalksLib.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.W2Lib.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LibAtomic.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptDefs.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptStructs.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptArith.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15LeptStderr.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15LeptBase.
Import V15CL7a.
Import V15CL8a.
Import V15CL3a.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptRoom.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Reloc.Reloc.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.RelocLept.
Import V15Kit.
(* [comment removed for export] *)










Import V15CL7a.V15LeptErr.

Import V15CL8a.V15LeptCmap.

Import V15CL3a.V15CmapFill.


Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].




Import V15Kit.V15Reloc. Import V15Kit.V15RelocCode. Import V15Kit.V15RelocSites. Import V15Kit.V15RelocImg. Import V15Kit.V15RelocVL.
Import V15Kit.V15RelocMusl. Import V15Kit.V15LeptEnv.
Import V15CL7a.V15LeptG.
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
Context {PINS : @LeptPins AL LLU16} {P16 : V15Pins}.
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
Proof. rl_tail (@LeptCmapDeser.blk_rdn v15_reloc v15_lept AL CL ASR PINS). Qed.

Theorem pixcmapDeserialize_W : forall C A m md regs (s dp nc : Z) (pb : word) (kb : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 160 + LSF <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x455c0 ->
  getr regs 10 = Z_to_bv 64 dp -> getr regs 11 = Z_to_bv 64 4 -> getr regs 12 = Z_to_bv 64 nc -> (1 <= nc <= 256)%Z ->
  live (c_A0 C) pb = Some kb -> (u pb <= dp)%Z -> (dp + 4 * nc <= u pb + kb)%Z ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_cmap <= kR)%Z -> (RB_cmap <= bR)%Z ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     ((getr regs' 10 = Z_to_bv 64 0 /\ forall q, live A' q = live A q)
      \/ (exists cm arr, getr regs' 10 = Z_to_bv 64 cm /\ cmapd_new C A A' m' cm arr nc)) ->
     aroom A' vm' (kR - RK_cmap) (bR - RB_cmap) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x198b4 : word) m al_rom) md) S.
Proof. rl_tail (@LeptCmapDeser.pixcmapDeserialize_W fx v15_reloc v15_code_vl v15_sites_vl v15_lept v15_img_vl v15_data v15_rw AL CL ASR PINS (v15_pinsG P16)). Qed.

End CmapDeser.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).      (* [comment removed for export] *)
End V15LeptCmapDeser.

From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require FPSteps.
Module V15LeptMask32_iface.
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
Import LinuxProcessSemantics.Riscv.Sem.
Import LinuxProcessSemantics.Riscv.Fpu.
Import OssFuzzTheorems.leptonica.grayquant_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CatExec.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CatSim.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.StepTac.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Hoare.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.ShapeAlg.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.AllocIface.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.PureModel.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.VmLedger.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.StoreOk.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.FPSteps.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocBase.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocSure.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.WalksLib.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptDefs.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptStructs.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptArith.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptRoom.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15LeptBase.
Import V15CL8a.
(* [comment removed for export] *)









Import V15CL8a.V15LeptPixHdr.
Import ListNotations.
Open Scope bv_scope.

Section Mask32Iface.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V15Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Definition band32_HEAD : Z := 124236.   Definition band32_EXIT : Z := 123752.   Definition band32_WIN : Z := 144.
Definition band32_CLOB : list reg := [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 19; 20; 21; 22; 23; 24; 25; 26; 28; 29; 30; 31]%bv.
Definition band32_loop_hop : Prop := forall (fx : FPState) C A Ar M md regs (s w h pixd datad datas : Z) (S : TSet),
  Cok C -> W C A M md -> sub_live Ar A -> (c_top C - LSTK + band32_WIN <= s)%Z -> (s <= c_top C)%Z -> (s mod 16 = 0)%Z ->
  hdr_ok w h 32 -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 datad) = Some (4 * (wpl_of w 1 * h))%Z -> live Ar (Z_to_bv 64 datad) = None -> live (c_A0 C) (Z_to_bv 64 datad) = None ->
  live A (Z_to_bv 64 datas) = Some (4 * (wpl_of w 32 * h))%Z ->
  Z_to_bv 64 datad <> Z_to_bv 64 datas -> (0 <= datad < 2 ^ 64)%Z -> (0 <= datas < 2 ^ 64)%Z -> (datad mod 16 = 0)%Z -> (datas mod 16 = 0)%Z ->
  getr regs 2 = Z_to_bv 64 (s + -144) -> getr regs 10 = Z_to_bv 64 (wpl_of w 1) -> getr regs 8 = Z_to_bv 64 (datas) -> getr regs 9 = Z_to_bv 64 (wpl_of w 32) -> getr regs 18 = Z_to_bv 64 (datad) -> getr regs 20 = Z_to_bv 64 (pixd) -> getr regs 22 = Z_to_bv 64 (18446744073709551615) -> getr regs 24 = Z_to_bv 64 (18446744073709551615) -> getr regs 25 = Z_to_bv 64 (18446744073709551615) -> getr regs 21 = Z_to_bv 64 (1) -> getr regs 23 = Z_to_bv 64 (1) -> getr regs 26 = Z_to_bv 64 (1) ->
  rdn SEGS M (Z_to_bv 64 (s + -128)) 4 = Some (Z_to_le_bytes 4 h) ->
  rdn SEGS M (Z_to_bv 64 (s + -124)) 4 = Some (Z_to_le_bytes 4 w) ->
  (forall regs' m', W C A m' md -> POSTM C Ar s M m' -> regs_agree (fun r => In r band32_CLOB) regs regs' -> getr regs' 10 = Z_to_bv 64 pixd ->
      (forall x : word, ~ (datad <= u x < datad + 4 * (wpl_of w 1 * h))%Z -> m' x = M x) ->
      realizes SEGS (mkCfg (@mkst fx regs' (Z_to_bv 64 band32_EXIT) m' al_rom) md) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (Z_to_bv 64 band32_HEAD) M al_rom) md) S.

(* [comment removed for export] *)
Definition discr32_HEAD : Z := 125124.   Definition discr32_EXIT : Z := 124936.   Definition discr32_WIN : Z := 208.
Definition discr32_CLOB : list reg := [1; 5; 6; 7; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 22; 23; 24; 25; 26; 27]%bv.
Definition discr32_loop_hop : Prop := forall (fx : FPState) C A Ar M md regs (s w h pixd datad datas : Z) (S : TSet),
  Cok C -> W C A M md -> sub_live Ar A -> (c_top C - LSTK + discr32_WIN <= s)%Z -> (s <= c_top C)%Z -> (s mod 16 = 0)%Z ->
  hdr_ok w h 32 -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 datad) = Some (4 * (wpl_of w 1 * h))%Z -> live Ar (Z_to_bv 64 datad) = None -> live (c_A0 C) (Z_to_bv 64 datad) = None ->
  live A (Z_to_bv 64 datas) = Some (4 * (wpl_of w 32 * h))%Z ->
  Z_to_bv 64 datad <> Z_to_bv 64 datas -> (0 <= datad < 2 ^ 64)%Z -> (0 <= datas < 2 ^ 64)%Z -> (datad mod 16 = 0)%Z -> (datas mod 16 = 0)%Z ->
  getr regs 2 = Z_to_bv 64 (s + -208) -> getr regs 10 = Z_to_bv 64 (wpl_of w 1) -> getr regs 20 = Z_to_bv 64 (datas) -> getr regs 19 = Z_to_bv 64 (wpl_of w 32) -> getr regs 21 = Z_to_bv 64 (datad) -> getr regs 18 = Z_to_bv 64 (pixd) -> getr regs 8 = Z_to_bv 64 (1) ->
  rdn SEGS M (Z_to_bv 64 (s + -112)) 4 = Some (Z_to_le_bytes 4 h) ->
  rdn SEGS M (Z_to_bv 64 (s + -108)) 4 = Some (Z_to_le_bytes 4 w) ->
  rdn SEGS M (Z_to_bv 64 (s + -120)) 4 = Some (Z_to_le_bytes 4 0) ->
  rdn SEGS M (Z_to_bv 64 (s + -124)) 4 = Some (Z_to_le_bytes 4 0) ->
  rdn SEGS M (Z_to_bv 64 (s + -128)) 4 = Some (Z_to_le_bytes 4 0) ->
  rdn SEGS M (Z_to_bv 64 (s + -132)) 4 = Some (Z_to_le_bytes 4 0) ->
  rdn SEGS M (Z_to_bv 64 (s + -136)) 4 = Some (Z_to_le_bytes 4 0) ->
  rdn SEGS M (Z_to_bv 64 (s + -140)) 4 = Some (Z_to_le_bytes 4 0) ->
  (forall regs' m', W C A m' md -> POSTM C Ar s M m' -> regs_agree (fun r => In r discr32_CLOB) regs regs' -> getr regs' 10 = Z_to_bv 64 pixd ->
      (forall x : word, ~ (datad <= u x < datad + 4 * (wpl_of w 1 * h))%Z -> ~ (s + -200 <= u x < s + -140)%Z -> m' x = M x) ->
      realizes SEGS (mkCfg (@mkst fx regs' (Z_to_bv 64 discr32_EXIT) m' al_rom) md) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (Z_to_bv 64 discr32_HEAD) M al_rom) md) S.

End Mask32Iface.
End V15LeptMask32_iface.

From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.VL Require LeptPixDestroy.
Module V15LeptPixDestroy.
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
Import OssFuzzTheorems.leptonica.grayquant_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CatExec.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CatSim.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.StepTac.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Hoare.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.ShapeAlg.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.AllocIface.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.PureModel.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.VmLedger.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.StoreOk.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.MemSplit.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.RefMemcpyLib.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.StartupTac.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.WalkTac.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocBase.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocSure.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.SumWalkTac.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.SumSpecs.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.WalksLib.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.W2Lib.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LibAtomic.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptDefs.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptStructs.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptArith.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15LeptStderr.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15LeptBase.
Import V15CL7a.
Import V15CL8a.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptRoom.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Reloc.Reloc.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.RelocLept.
Import V15Kit.
(* [comment removed for export] *)










Import V15CL7a.V15LeptErr.

Import V15CL8a.V15LeptCmap.


Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].




Import V15Kit.V15Reloc. Import V15Kit.V15RelocCode. Import V15Kit.V15RelocSites. Import V15Kit.V15RelocImg. Import V15Kit.V15RelocVL.
Import V15Kit.V15RelocMusl. Import V15Kit.V15LeptEnv.
Import V15CL7a.V15LeptG.
Import ListNotations.
Open Scope bv_scope.

Section PixDestroy.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V15Pins}.
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
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x455c0 -> (pp mod 8 = 0)%Z ->
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
  realizes SEGS (mkCfg (mkst regs (0x170a4 : word) m al_rom) md) S.
Proof. rl_tail (@LeptPixDestroy.pixDestroy_W fx v15_reloc v15_sites v15_code_vl v15_sites_vl v15_lept v15_img_vl v15_data v15_rw AL CL ASR PINS (v15_pinsG P16)). Qed.

End PixDestroy.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).      (* [comment removed for export] *)
End V15LeptPixDestroy.
