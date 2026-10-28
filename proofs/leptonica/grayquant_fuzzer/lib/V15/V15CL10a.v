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
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15CL9a.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15CL3a.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptRoom.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require LiaFast.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Reloc Require Reloc.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require RelocLept.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.VL Require LeptCmapValid.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15Kit.
Module V15LeptCmapValid.
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
Import V15CL9a.
Import V15CL3a.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptRoom.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Reloc.Reloc.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.RelocLept.
Import V15Kit.
(* [comment removed for export] *)










Import V15CL7a.V15LeptErr.

Import V15CL8a.V15LeptCmap.

Import V15CL9a.V15LeptCmapDeser.

Import V15CL3a.V15MaxIndex.


Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].




Import V15Kit.V15Reloc. Import V15Kit.V15RelocCode. Import V15Kit.V15RelocSites. Import V15Kit.V15RelocImg. Import V15Kit.V15RelocVL.
Import V15Kit.V15RelocMusl. Import V15Kit.V15LeptEnv.
Import V15CL7a.V15LeptG.
Import ListNotations.
Open Scope bv_scope.

Section CmapValid.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V15Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
Definition cmap_ok (cv : cmapv) : Prop :=
  (c_d cv = 1 \/ c_d cv = 2 \/ c_d cv = 4 \/ c_d cv = 8)%Z /\ c_nalloc cv = (2 ^ c_d cv)%Z /\ (1 <= c_n cv <= c_nalloc cv)%Z /\ (1 <= c_arr cv)%Z.
Definition pv_post (C : lctx) (A : AS) (s : Z) (m m' : word -> option byte) (pv valid : Z) : Prop :=
  POSTM C A s (wbytes m (Z_to_bv 64 pv) (word_to_le_bytes 4 (Z_to_bv 64 valid))) m'.
Theorem pixcmapIsValid_null_W : forall C A m md regs (s cm pv : Z) (cv : cmapv) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 48 <= s)%Z -> (s <= pv)%Z -> (pv + 4 <= c_top C)%Z -> (pv mod 4 = 0)%Z ->
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = Z_to_bv 64 cm -> getr regs 11 = Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 pv ->
  CMAPat m cm cv -> cmap_ok cv -> live A (Z_to_bv 64 cm) = Some 24%Z ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> pv_post C A s m m' pv 1 -> getr regs' 10 = Z_to_bv 64 0 ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (0x18888 : word) m al_rom) md) S.
Proof. rl_tail (@LeptCmapValid.pixcmapIsValid_null_W fx v15_reloc v15_code_vl v15_lept AL CL ASR PINS (v15_pinsG P16)). Qed.

Theorem pixcmapIsValid_pix_W : forall C A m md regs (s cm pix pv : Z) (cv : cmapv) (v : pixv) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 48 + LSF <= s)%Z -> (s <= pv)%Z -> (pv + 4 <= c_top C)%Z -> (pv mod 4 = 0)%Z ->
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = Z_to_bv 64 cm -> getr regs 11 = Z_to_bv 64 pix -> getr regs 12 = Z_to_bv 64 pv ->
  CMAPat m cm cv -> cmap_ok cv -> live A (Z_to_bv 64 cm) = Some 24%Z ->
  PIXat m pix v -> live A (Z_to_bv 64 pix) = Some 64%Z ->
  dval (p_d v) -> (1 <= p_w v <= 20000)%Z -> (1 <= p_h v <= 20000)%Z -> p_wpl v = wpl_of (p_w v) (p_d v) ->
  live A (Z_to_bv 64 (p_data v)) = Some (4 * (p_wpl v * p_h v))%Z ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' ->
     (exists valid, (valid = 0 \/ valid = 1)%Z /\ pv_post C A s m m' pv valid /\ getr regs' 10 = Z_to_bv 64 (1 - valid)) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (0x18888 : word) m al_rom) md) S.
Proof. rl_tail (@LeptCmapValid.pixcmapIsValid_pix_W fx v15_reloc v15_code v15_sites v15_code_vl v15_sites_vl v15_lept v15_img_vl v15_data v15_img v15_rw v15_pf v15_lenv_vl AL CL ASR PINS (v15_pinsG P16)). Qed.

Lemma POSTM_absorb : forall C Ar A M md m2 (s s' : Z) (a : word) bs, Cok C -> W C A M md -> sub_live Ar A ->
  (s' <= s)%Z -> (c_top C - LSTK <= u a)%Z -> (u a + Z.of_nat (length bs) <= s)%Z -> (s <= c_top C)%Z ->
  POSTM C A s' (wbytes M a bs) m2 -> POSTM C Ar s M m2.
Proof. rl_tail (@LeptCmapValid.POSTM_absorb v15_reloc v15_lept AL CL ASR PINS). Qed.

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
  realizes SEGS (mkCfg (mkst regs (0x176bc : word) m al_rom) md) S.
Proof. rl_tail (@LeptCmapValid.pixSetColormap_W fx v15_reloc v15_code_vl v15_sites_vl v15_lept AL CL ASR PINS (v15_pinsG P16)). Qed.

End CmapValid.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).      (* [comment removed for export] *)
End V15LeptCmapValid.

From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptArith2.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15LeptPadBitsW.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15LeptPixCreate.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15LeptPixHdrS.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptRoom14.
Module V15LeptPixCreateS.
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
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptArith2.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15LeptStderr.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15LeptBase.
Import V15CL7a.
Import V15CL8a.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15LeptPadBitsW.
Import V15Kit.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15LeptPixCreate.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15LeptPixHdrS.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptRoom.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptRoom14.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)









Import V15CL7a.V15LeptErr.

Import V15CL8a.V15LeptPixHdr.


Import V15Kit.V15Memset.



Import ListNotations.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].

Section PixCreate.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V15Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
#[local] Abbreviation FR4 := (V15LeptPixCreate.FR4).

Theorem pixCreateNoInit_sure_W : forall C A m md regs (s w h d : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 96 + LSF <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x455c0 ->
  getr regs 10 = Z_to_bv 64 w -> getr regs 11 = Z_to_bv 64 h -> getr regs 12 = Z_to_bv 64 d ->
  (1 <= w)%Z -> (1 <= h)%Z -> hdr_ok w h d ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_pix <= kR)%Z -> (RB_pix14 <= bR)%Z ->
  (forall A' m' vm' regs' (pix data : Z), W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     getr regs' 10 = Z_to_bv 64 pix -> pixr_new C A A' m' pix data (set_data (pix_hdr w h d) data) ->
     aroom A' vm' (kR - RK_pix) (bR - RB_pix14) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x16bec : word) m al_rom) md) S.
Proof.
  intros C A m md regs s w h d ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 H12 Hw1 Hh1 HOK0 kR bR Hrm Hrk Hrb HK.
  assert (Hw : (1 <= w <= 1000000)%Z) by (destruct HOK0 as (_ & X & _); lia). assert (Hh : (1 <= h <= 1000000)%Z) by (destruct HOK0 as (_ & _ & X & _); lia).
  assert (Hwh : (w * h <= 400000000)%Z) by (destruct HOK0 as (_ & X & Y & _); nia).
  assert (Hd : (0 <= d < 2 ^ 64)%Z) by (destruct HOK0 as (X & _); pose proof (dval_range d X); lia).
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold LSF in *.
  pose proof (W_sok_win C A m md (s - 32) 32 CK HW ltac:(lia) ltac:(cbn; lia)) as SOK.
  destruct (pn_A al_rom regs m s w h d ret ltac:(lia) ltac:(lia) SOK H2 H1 H10 H11 H12) as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q12 & Q9 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  assert (WP1 : W C A (FR4 m s ret regs) md /\ POSTM C A s m (FR4 m s ret regs)) by (unfold FR4; wp_win CK).
  destruct WP1 as [HW1 PM1]. set (M1 := FR4 m s ret regs) in *.
  pose proof (cells4_FR4 m s ret regs ltac:(lia) ltac:(lia)) as CE1. fold M1 in CE1.
  assert (Q4 : getr r1 4 = Z_to_bv 64 0x455c0) by (csr; reflexivity).
  apply (pixCreateHeader_sure_W C A M1 md r1 (s - 32) w h d (Z_to_bv 64 0x16c04) S CK HW1 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold LSF; lia) ltac:(lia) Q1 ltac:(red; apply bv_eq; reflexivity) Q4 Q10 Q11 Q12 Hw1 Hh1 HOK0 kR bR Hrm ltac:(unfold RK_hdr, RK_pix in *; lia) ltac:(unfold RB_hdr, RB_pix14 in *; lia)).
  intros A1 m1 vm1 r2 pix HWa CSa PMa Hres PN Hrma.
  replace (Z_to_bv 64 0x16c04) with (0x16c04 : word) by (apply bv_eq; reflexivity).
  assert (PMa' : POSTM C A s m m1) by (eapply POSTM_trans; [exact PM1 | eapply POSTM_mono; [|exact PMa]; lia]).
  pose proof (cells4_frm C (s - 32) M1 m1 s _ _ _ CK (proj1 PMa) ltac:(lia) ltac:(lia) ltac:(lia) CE1) as CE2.
  assert (E2 : getr r2 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
  assert (E9 : getr r2 9 = Z_to_bv 64 h) by (csr; reflexivity).
  assert (E4 : getr r2 4 = Z_to_bv 64 0x455c0) by (csr; reflexivity).
  - (* [comment removed for export] *)
    pose proof HOK0 as (DV & Hw2 & Hh2 & Hsz). destruct PN as (Gp & TOPp & ALp & L0 & L00 & L1 & LEQ & PX1).
    pose proof (dval_range d DV) as Hd32. pose proof (wpl_of_range w d ltac:(lia) DV) as Hwpl.
    pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
    assert (AL8 : (pix mod 8 = 0)%Z) by (rewrite <- (Z.add_0_r pix); apply mod16_plus_mod8; [exact ALp | reflexivity]).
    destruct (pn_B al_rom r2 m1 s h pix (pix_hdr w h d) PX1 eq_refl ltac:(lia) ltac:(cbn; lia) Gp AL8 (W_pmm_malloc C A1 m1 _ HWa) Hres E9)
      as (r3 & RUN3 & V10 & V1 & V8 & V9 & AG3).
    cbn [p_wpl pix_hdr] in V10.
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN3 |].
    assert (V4 : getr r3 4 = Z_to_bv 64 0x455c0) by (csr; reflexivity).
    assert (V2 : getr r3 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
    replace (0x28b94 : word) with (Z_to_bv 64 0x28b94) by (apply bv_eq; reflexivity).
    apply (W_malloc16_sure C A1 m1 _ r3 (4 * (wpl_of w d * h)) (kR - RK_hdr) (bR - RB_hdr) (Z_to_bv 64 0x16c3c) (s - 32) S CK HWa V10 ltac:(lia) ltac:(rewrite with_vmmaps_vmmaps; exact Hrma) ltac:(unfold RK_hdr, RK_pix in *; lia) ltac:(pose proof (alloc_margin_le (4 * (wpl_of w d * h))); unfold RB_hdr, RB_pix14 in *; lia) ltac:(unfold ROOM_NMAX; lia) V1
             ltac:(red; apply bv_eq; reflexivity) V4 V2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)).
    intros A2 m2 vm2 r4 res HWb Hres2 CSb Hnz K0 K1 K00 KEQ AL16 TOP PMb Hrmb. rewrite with_vmmaps_twice. rewrite with_vmmaps_twice in HWb.
    replace (Z_to_bv 64 0x16c3c) with (0x16c3c : word) by (apply bv_eq; reflexivity).
    assert (SUBa : sub_live A A1) by (eapply sub_live_new; eassumption).
    assert (PMb' : POSTM C A s m m2).
    { eapply POSTM_trans; [exact PMa'|]. apply (POSTM_sub C A A1 _ _ _ SUBa). eapply POSTM_mono; [|exact PMb]. lia. }
    pose proof (cells4_frm C (s - 32) m1 m2 s _ _ _ CK (proj1 PMb) ltac:(lia) ltac:(lia) ltac:(lia) CE2) as CE3.
    assert (PX2 : PIXat m2 pix (pix_hdr w h d)).
    { apply (PIXat_frame m1); [exact PX1|]. intros x Hx. pose proof (proj2 PMb (Z_to_bv 64 pix) 64%Z (u x - pix)%Z L1 ltac:(lia)) as E.
      unfold at_ in E. rewrite u_Z2bv in E by lia. replace (pix + (u x - pix))%Z with (u x) in E by lia. rewrite zbv_self in E. exact E. }
    assert (X8 : getr r4 8 = Z_to_bv 64 pix) by (csr; reflexivity).
    assert (X2 : getr r4 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
    assert (X4 : getr r4 4 = Z_to_bv 64 0x455c0) by (csr; reflexivity).
    assert (SOKp : store_ok SEGS m2 (Z_to_bv 64 pix) 64 = true).
    { rewrite <- p16_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx.
      unfold wview. destruct (m2 x) eqn:E; [discriminate|]. exfalso. exact (PIXat_defined m2 pix _ x PX2 ltac:(lia) E). }
    + (* [comment removed for export] *)
      assert (Hdat : (4096 <= u res)%Z /\ (u res + 4 * (wpl_of w d * h) <= alloc_top (c_vm C))%Z).
      { destruct (blk_range C A2 m2 _ res _ CK HWb K1 ltac:(lia)) as [G1 G2]. lia. }
      assert (Eres : res = Z_to_bv 64 (u res)) by (symmetry; apply zbv_self).
      set (data := u res) in *. clearbody data.
      rewrite Eres in Hres2, K0, K1, K00, KEQ.
      assert (NEpd : Z_to_bv 64 pix <> Z_to_bv 64 data) by (intros E; rewrite E in L1; congruence).
      assert (NEpd' : pix <> data) by (intros E; apply NEpd; rewrite E; reflexivity).
      assert (Lp2 : live A2 (Z_to_bv 64 pix) = Some 64%Z) by (rewrite (KEQ _ NEpd); exact L1).
      assert (LAd : live A (Z_to_bv 64 data) = None) by (rewrite <- (LEQ _ (not_eq_sym NEpd)); exact K0).
      assert (SUBb : sub_live A A2) by (eapply sub_live_trans; [exact SUBa | eapply sub_live_new; eassumption]).
      destruct (pn_C al_rom r4 m2 pix data Gp ltac:(lia) ltac:(lia) SOKp Hres2 X8) as (r5 & RUN5 & Y10 & Y11 & Y1 & Y8 & AG5).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWb)) | exact (mp_lazy _ (w_pure _ _ _ _ HWb)) | exact RUN5 |].
      match goal with |- realizes _ (mkCfg (mkst _ _ ?MM _) _) _ => set (M3 := MM) end.
      assert (WP3 : W C A2 M3 (with_vmmaps vm2 md) /\ POSTM C A s m M3).
      { subst M3. apply (WP_blk C A A2 m _ _ (Z_to_bv 64 pix) _ 64); [exact CK | | exact Lp2 | exact L0 | exact L00 | exact SUBb | rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia].
        split; [exact HWb | exact PMb']. }
      destruct WP3 as [HW3 PM3].
      assert (PX3 : PIXat M3 pix (set_data (pix_hdr w h d) data)) by (subst M3; apply PIX_wr_data; [exact PX2 | lia]).
      assert (Y2 : getr r5 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
      apply (padbits_W C A A2 M3 _ r5 (s - 32) pix (set_data (pix_hdr w h d) data) (Z_to_bv 64 0x16c50) S CK HW3 SUBb Y2
               ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold LSF; lia) ltac:(lia) Y1 ltac:(red; apply bv_eq; reflexivity) Y10 Y11
               PX3 DV ltac:(cbn; lia) ltac:(cbn; lia) eq_refl Lp2).
      { cbn. exact K1. } { cbn. exact LAd. } { cbn. exact K00. } { cbn. exact NEpd. }
      intros m5 r6 HW5 CS5 PM5 PX5 OUT5 A10.
      replace (Z_to_bv 64 0x16c50) with (0x16c50 : word) by (apply bv_eq; reflexivity).
      assert (CE5 : cells4 m5 s ret (getr regs 8) (getr regs 9)).
      { apply (cells4_frm C (s - 32) M3 m5 s); [exact CK | exact (proj1 PM5) | lia | lia | lia |].
        subst M3. destruct CE3 as (C1 & C2 & C3). unfold cells4. repeat split; repeat rdn_peel1; assumption. }
      destruct CE5 as (C1 & C2 & C3).
      assert (W2 : getr r6 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
      assert (W8 : getr r6 8 = Z_to_bv 64 pix) by (csr; reflexivity).
      destruct (pn_D al_rom r6 m5 s pix ret _ _ ltac:(lia) ltac:(lia) Hret C1 C2 C3 W2 W8) as (r7 & RUN7 & U2 & U1 & U10 & U8 & U9 & AG7).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW5)) | exact (mp_lazy _ (w_pure _ _ _ _ HW5)) | exact RUN7 |].
      apply (HK A2 m5 vm2 r7 pix data HW5).
      5:{ pose proof (alloc_margin_le (4 * (wpl_of w d * h))). apply (aroom_mono _ _ _ _ _ _ Hrmb); unfold RK_hdr, RK_pix, RB_hdr, RB_pix14 in *; lia. }
      * apply cs_kept_intro; csr; try reflexivity.
      * eapply POSTM_trans; [exact PM3 | eapply POSTM_mono; [|exact PM5]; lia].
      * exact U10.
      * unfold pixr_new. cbn [p_wpl p_h p_data set_data pix_hdr].
        do 15 (try (split; [first [assumption | lia | idtac] |])).
        all: try assumption; try lia; try reflexivity.
        all: intros q N1 N2; rewrite (KEQ q N2); apply LEQ; exact N1.
Qed.

Theorem pixCreate_sure_W : forall C A m md regs (s w h d : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 112 + LSF <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x455c0 ->
  getr regs 10 = Z_to_bv 64 w -> getr regs 11 = Z_to_bv 64 h -> getr regs 12 = Z_to_bv 64 d ->
  (1 <= w)%Z -> (1 <= h)%Z -> hdr_ok w h d ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_pix <= kR)%Z -> (RB_pix14 <= bR)%Z ->
  (forall A' m' vm' regs' (pix data : Z), W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     getr regs' 10 = Z_to_bv 64 pix -> pixr_new C A A' m' pix data (set_data (pix_hdr w h d) data) ->
     aroom A' vm' (kR - RK_pix) (bR - RB_pix14) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x16b48 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s w h d ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 H12 Hw1 Hh1 HOK0 kR bR Hrm Hrk Hrb HK.
  assert (Hw : (1 <= w <= 1000000)%Z) by (destruct HOK0 as (_ & X & _); lia). assert (Hh : (1 <= h <= 1000000)%Z) by (destruct HOK0 as (_ & _ & X & _); lia).
  assert (Hwh : (w * h <= 400000000)%Z) by (destruct HOK0 as (_ & X & Y & _); nia).
  assert (Hd : (0 <= d < 2 ^ 64)%Z) by (destruct HOK0 as (X & _); pose proof (dval_range d X); lia).
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold LSF in *.
  pose proof (W_sok_win C A m md (s - 16) 16 CK HW ltac:(lia) ltac:(cbn; lia)) as SOK.
  destruct (pk_A al_rom regs m s ret ltac:(lia) ltac:(lia) SOK H2 H1) as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q12 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  set (M1 := wbytes (wbytes m _ _) _ _).
  assert (WP1 : W C A M1 md /\ POSTM C A s m M1) by (subst M1; wp_win CK).
  destruct WP1 as [HW1 PM1].
  assert (Q4 : getr r1 4 = Z_to_bv 64 0x455c0) by (csr; reflexivity).
  rewrite H10 in Q10. rewrite H11 in Q11. rewrite H12 in Q12.
  apply (pixCreateNoInit_sure_W C A M1 md r1 (s - 16) w h d (Z_to_bv 64 0x16b58) S CK HW1 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold LSF; lia) ltac:(lia) Q1 ltac:(red; apply bv_eq; reflexivity) Q4 Q10 Q11 Q12 Hw1 Hh1 HOK0 kR bR Hrm ltac:(unfold RK_hdr, RK_pix in *; lia) ltac:(unfold RB_hdr, RB_pix14 in *; lia)).
  intros A1 m1 vm1 r2 pix data HWa CSa PMa Hres PN Hrma.
  replace (Z_to_bv 64 0x16b58) with (0x16b58 : word) by (apply bv_eq; reflexivity).
  assert (PMa' : POSTM C A s m m1) by (eapply POSTM_trans; [exact PM1 | eapply POSTM_mono; [|exact PMa]; lia]).
  assert (R8 : rdn SEGS m1 (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret)).
  { rewrite (FRM_rdn16 C (s - 16) M1 m1 (s - 8) 8 CK (proj1 PMa)) by (cbn; lia). subst M1. rdn_solve. }
  assert (R16 : rdn SEGS m1 (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8))).
  { rewrite (FRM_rdn16 C (s - 16) M1 m1 (s - 16) 8 CK (proj1 PMa)) by (cbn; lia). subst M1. rdn_solve. }
  assert (E2 : getr r2 2 = Z_to_bv 64 (s - 16)) by (csr; reflexivity).
  - pose proof HOK0 as (DV & Hw2 & Hh2 & Hsz).
    destruct PN as (Gp & TOPp & ALp & Gd & TOPd & ALd & NEpd & L0 & K0 & L00 & K00 & L1 & K1 & LEQ & PX1 & Hdata).
    cbn [p_wpl p_h p_data set_data pix_hdr] in TOPd, K1, Hdata.
    pose proof (dval_range d DV) as Hd32. pose proof (wpl_of_range w d ltac:(lia) DV) as Hwpl.
    pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
    assert (AL8 : (pix mod 8 = 0)%Z) by (rewrite <- (Z.add_0_r pix); apply mod16_plus_mod8; [exact ALp | reflexivity]).
    destruct (pk_B al_rom r2 m1 pix _ PX1 Gp ltac:(cbn; lia) ltac:(cbn; lia) AL8 Hres) as (r3 & RUN3 & V10 & V11 & V12 & V1 & V8 & AG3).
    cbn [p_wpl p_h p_data set_data pix_hdr] in V10, V12.
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN3 |].
    assert (SOKd : store_ok SEGS m1 (Z_to_bv 64 data) (Z.to_nat (4 * (wpl_of w d * h))) = true).
    { rewrite <- p16_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [lia|]. intros x Hx.
      unfold wview. destruct (m1 x) eqn:E; [discriminate|]. exfalso.
      destruct (blk_byte C A1 m1 _ (Z_to_bv 64 data) _ x CK HWa K1 ltac:(rewrite u_Z2bv by lia; lia)) as (_ & D & _). exact (D E). }
    apply (memset_at (with_vmmaps vm1 md) r3 m1 al_rom data (4 * (wpl_of w d * h)) (Z_to_bv 64 0x16b94) S
             (md_pure_with_vmmaps _ _ (w_pure _ _ _ _ HW)) ltac:(lia) ltac:(lia) ltac:(lia) SOKd ltac:(red; apply bv_eq; reflexivity) V1 V10 V11 V12).
    intros r4 A10' AG4.
    replace (Z_to_bv 64 0x16b94) with (0x16b94 : word) by (apply bv_eq; reflexivity).
    set (M5 := zf m1 data [(0, 4 * (wpl_of w d * h))%Z]).
    assert (OUT5 : forall x : word, (u x < data \/ data + 4 * (wpl_of w d * h) <= u x)%Z -> M5 x = m1 x).
    { intros x Hx. subst M5. apply zf_outside. apply inzr_falseP. cbn [inzrP]. lia. }
    assert (CH : forall a, M5 a <> m1 a -> scratch C s a \/ (exists p n, live A1 p = Some n /\ live A p = None /\ (u p <= u a < u p + n)%Z)).
    { intros a NE. right. exists (Z_to_bv 64 data), (4 * (wpl_of w d * h))%Z. rewrite u_Z2bv by lia. split; [exact K1 | split; [exact K0|]].
      destruct (Z_lt_ge_dec (u a) data); [exfalso; apply NE; apply OUT5; lia|].
      destruct (Z_lt_ge_dec (u a) (data + 4 * (wpl_of w d * h))); [lia | exfalso; apply NE; apply OUT5; lia]. }
    assert (HW5 : W C A1 M5 (with_vmmaps vm1 md)).
    { apply (W_local C A1 m1 _ M5 s CK HWa Hhi); [| subst M5; apply zf_grows].
      intros a NE. destruct (CH a NE) as [X|(p & n & L & _ & R)]; [left; exact X | right; exists p, n]. split; [exact L | split; [| exact R]].
      destruct (bv_eq_dec _ p (Z_to_bv 64 data)) as [->|NE']; [exact K00|].
      exfalso. (* [comment removed for export] *) apply NE. apply OUT5.
      pose proof (ai_live_disjoint A1 m1 _ _ _ _ _ (w_inv _ _ _ _ HWa) L K1 NE') as D. rewrite u_Z2bv in D by lia.
      pose proof (ai_live_hull A1 m1 _ _ _ (w_inv _ _ _ _ HWa) L) as (Hn0 & _). pose proof (round16_ge n Hn0).
      pose proof (round16_ge (4 * (wpl_of w d * h)) ltac:(lia)). lia. }
    assert (PM5 : POSTM C A s m M5).
    { eapply POSTM_trans; [exact PMa'|]. exact (POSTM_local C A A1 m1 _ M5 s CK HWa (sub_live_new2 _ _ _ _ _ _ L0 K0 L1 K1 LEQ) CH). }
    assert (PX5 : PIXat M5 pix (set_data (pix_hdr w h d) data)).
    { apply (PIXat_frame m1); [exact PX1|]. intros x Hx. apply OUT5.
      pose proof (ai_live_disjoint A1 m1 _ _ _ _ _ (w_inv _ _ _ _ HWa) L1 K1 (zneq_w pix data ltac:(lia) ltac:(lia) NEpd)) as D. rewrite !u_Z2bv in D by lia.
      unfold round16 in D at 1. change ((64 + 15) / 16)%Z with 4%Z in D. pose proof (round16_ge (4 * (wpl_of w d * h)) ltac:(lia)). lia. }
    assert (W2 : getr r4 2 = Z_to_bv 64 (s - 16)) by (csr; reflexivity).
    assert (W8 : getr r4 8 = Z_to_bv 64 pix) by (csr; reflexivity).
    destruct (pk_C al_rom r4 M5 s pix ret (getr regs 8) ltac:(lia) ltac:(lia) Hret) as (r5 & RUN5 & U2 & U1 & U10 & U8 & AG5).
    { rewrite <- R8. apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx. apply OUT5. lia. }
    { rewrite <- R16. apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx. apply OUT5. lia. }
    { exact W2. } { exact W8. }
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW5)) | exact (mp_lazy _ (w_pure _ _ _ _ HW5)) | exact RUN5 |].
    apply (HK A1 M5 vm1 r5 pix data HW5).
    5:{ exact Hrma. }
    + apply cs_kept_intro; csr; try reflexivity.
    + exact PM5.
    + exact U10.
    + unfold pixr_new. cbn [p_wpl p_h p_data set_data pix_hdr]. repeat (split; [first [assumption | lia] |]); try assumption.
      all: first [exact PX5 | reflexivity | assumption].
Qed.

End PixCreate.
End V15LeptPixCreateS.
