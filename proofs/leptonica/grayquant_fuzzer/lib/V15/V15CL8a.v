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
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptDefs.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptStructs.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15LeptStderr.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15LeptBase.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15CL7a.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptRoom.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Reloc Require Reloc.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require RelocLept.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.VL Require LeptCmap.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15Kit.
Module V15LeptCmap.
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
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptDefs.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptStructs.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15LeptStderr.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15LeptBase.
Import V15CL7a.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptRoom.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Reloc.Reloc.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.RelocLept.
Import V15Kit.
(* [comment removed for export] *)










Import V15CL7a.V15LeptErr.





Import V15Kit.V15Reloc. Import V15Kit.V15RelocCode. Import V15Kit.V15RelocSites. Import V15Kit.V15RelocImg. Import V15Kit.V15RelocVL.
Import V15Kit.V15RelocMusl. Import V15Kit.V15LeptEnv.
Import V15CL7a.V15LeptG.
Import ListNotations.
Open Scope bv_scope.

Lemma sllw_1 : forall d, (d = 1 \/ d = 2 \/ d = 4 \/ d = 8)%Z -> v_sllw (Z_to_bv 64 1) (Z_to_bv 64 d) = Z_to_bv 64 (2 ^ d).
Proof. rl_tail (@LeptCmap.sllw_1). Qed.

Section Cmap.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V15Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
Theorem pixcmapDestroy_W : forall C A m md regs (s pp cm : Z) (cv : cmapv) (k : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 32 + ALLOC_STACK <= s)%Z -> (s <= pp)%Z -> (pp + 8 <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x455c0 -> (pp mod 8 = 0)%Z ->
  getr regs 10 = Z_to_bv 64 pp -> rdn SEGS m (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 cm) ->
  CMAPat m cm cv -> live A (Z_to_bv 64 cm) = Some 24%Z -> live A (Z_to_bv 64 (c_arr cv)) = Some k ->
  live (c_A0 C) (Z_to_bv 64 cm) = None -> live (c_A0 C) (Z_to_bv 64 (c_arr cv)) = None -> cm <> c_arr cv ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' ->
     live A' (Z_to_bv 64 cm) = None -> live A' (Z_to_bv 64 (c_arr cv)) = None ->
     (forall q, q <> Z_to_bv 64 cm -> q <> Z_to_bv 64 (c_arr cv) -> live A' q = live A q) ->
     POSTM C A' (pp + 8) m m' ->
     rdn SEGS m' (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 0) ->
     roomtr A (m_vmmaps md) A' vm' 0 0 ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x18ba0 : word) m al_rom) md) S.
Proof. rl_tail (@LeptCmap.pixcmapDestroy_W fx v15_reloc v15_code_vl v15_sites_vl v15_lept AL CL ASR PINS (v15_pinsG P16)). Qed.

End Cmap.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).      (* [comment removed for export] *)
End V15LeptCmap.

From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LibAtomic.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptArith.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptArith2.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.VL Require LeptDeserA.
Module V15LeptDeserA.
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
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptRoom.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Reloc.Reloc.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.RelocLept.
Import V15Kit.
(* [comment removed for export] *)










Import V15CL7a.V15LeptErr.





Import V15Kit.V15Reloc. Import V15Kit.V15RelocCode. Import V15Kit.V15RelocSites. Import V15Kit.V15RelocImg. Import V15Kit.V15RelocVL.
Import V15Kit.V15RelocMusl. Import V15Kit.V15LeptEnv.
Import V15CL7a.V15LeptG.
Import ListNotations.
Open Scope bv_scope.

Section DeserA.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V15Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
Section Segs.
Variable rom : word -> option byte.
Definition FR9 (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
       (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
       (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
       (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)))
       (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr regs 18)))
       (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (getr regs 19)))
       (Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (getr regs 20)))
       (Z_to_bv 64 (s - 56)) (word_to_le_bytes 8 (getr regs 21)))
       (Z_to_bv 64 (s - 64)) (word_to_le_bytes 8 (getr regs 22)))
       (Z_to_bv 64 (s - 72)) (word_to_le_bytes 8 (getr regs 23)).
Lemma pd_A0 : forall regs m (s dp nb : Z) (ret : word),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= dp < 2 ^ 64)%Z -> (0 <= nb < 2 ^ 31)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 96)) 96 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 dp -> getr regs 11 = Z_to_bv 64 nb ->
    exists regs',
      msteps SEGS (mkst regs (0x27928 : word) m rom) (mkst regs' (0x27960 : word) (FR9 m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 96) /\ getr regs' 10 = Z_to_bv 64 dp /\ getr regs' 11 = Z_to_bv 64 nb
      /\ getr regs' 12 = Z_to_bv 64 18446744071562067995 /\ getr regs' 13 = Z_to_bv 64 (nb + 18446744071562067968)
      /\ regs_agree (fun r => In r [2; 12; 13]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_A0 fx v15_reloc v15_code_vl rom). Qed.

Lemma pd_A1 : forall regs m (nb : Z),
    (28 <= nb < 2 ^ 31)%Z -> getr regs 12 = Z_to_bv 64 18446744071562067995 -> getr regs 13 = Z_to_bv 64 (nb + 18446744071562067968) ->
    exists regs', msteps SEGS (mkst regs (0x27960 : word) m rom) (mkst regs' (0x279c0 : word) m rom) /\ regs_agree (fun r => False) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_A1 fx v15_reloc v15_code_vl rom). Qed.

Lemma pd_A2 : forall regs m (nb : Z),
    (0 <= nb < 28)%Z -> getr regs 12 = Z_to_bv 64 18446744071562067995 -> getr regs 13 = Z_to_bv 64 (nb + 18446744071562067968) ->
    getr regs 11 = Z_to_bv 64 nb ->
    rdn SEGS m (Z_to_bv 64 0x341f8) 8 = Some (Z_to_le_bytes 8 0x35268) -> rdn SEGS m (Z_to_bv 64 0x35268) 4 = Some (Z_to_le_bytes 4 3) ->
    exists regs',
      msteps SEGS (mkst regs (0x27960 : word) m rom) (mkst regs' (0x15520 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 0x10cf9 /\ getr regs' 11 = Z_to_bv 64 0x10a51 /\ getr regs' 12 = Z_to_bv 64 nb /\ getr regs' 1 = Z_to_bv 64 0x27994
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_A2 fx v15_reloc v15_code_vl v15_sites_vl rom). Qed.

Lemma pd_B : forall regs m (dp : Z) (b0 b1 b2 b3 : byte),
    (1 <= dp)%Z -> (dp + 28 <= 2 ^ 64)%Z -> (dp mod 4 = 0)%Z ->
    rdn SEGS m (Z_to_bv 64 dp) 1 = Some [b0] -> rdn SEGS m (Z_to_bv 64 (dp + 1)) 1 = Some [b1] ->
    rdn SEGS m (Z_to_bv 64 (dp + 2)) 1 = Some [b2] -> rdn SEGS m (Z_to_bv 64 (dp + 3)) 1 = Some [b3] ->
    u b0 = 115%Z -> u b1 = 112%Z -> u b2 = 105%Z -> u b3 = 120%Z ->
    getr regs 10 = Z_to_bv 64 dp ->
    exists regs', msteps SEGS (mkst regs (0x279c0 : word) m rom) (mkst regs' (0x27a58 : word) m rom)
      /\ getr regs' 12 = Z_to_bv 64 (dp + 20) /\ getr regs' 13 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [12; 13]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_B fx v15_reloc v15_code_vl rom). Qed.

Lemma pd_Bbad : forall regs m (dp : Z) (b0 b1 b2 b3 : byte),
    (1 <= dp)%Z -> (dp + 28 <= 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 dp) 1 = Some [b0] -> rdn SEGS m (Z_to_bv 64 (dp + 1)) 1 = Some [b1] ->
    rdn SEGS m (Z_to_bv 64 (dp + 2)) 1 = Some [b2] -> rdn SEGS m (Z_to_bv 64 (dp + 3)) 1 = Some [b3] ->
    ~ (u b0 = 115 /\ u b1 = 112 /\ u b2 = 105 /\ u b3 = 120)%Z ->
    getr regs 10 = Z_to_bv 64 dp ->
    exists regs', msteps SEGS (mkst regs (0x279c0 : word) m rom) (mkst regs' (0x27a94 : word) m rom)
      /\ regs_agree (fun r => In r [12; 13]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_Bbad fx v15_reloc v15_code_vl rom). Qed.

Lemma pd_C : forall regs m (dp wr : Z) bs4,
    (1 <= dp)%Z -> (dp + 28 <= 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (dp + 4)) 4 = Some bs4 -> bytes_le_to_Z bs4 = wr -> (1 <= wr <= 1000000)%Z ->
    getr regs 10 = Z_to_bv 64 dp ->
    exists regs', msteps SEGS (mkst regs (0x27a58 : word) m rom) (mkst regs' (0x27ae8 : word) m rom)
      /\ getr regs' 9 = Z_to_bv 64 wr /\ getr regs' 13 = Z_to_bv 64 18446744073708551615
      /\ regs_agree (fun r => In r [9; 13; 14]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_C fx v15_reloc v15_code_vl rom). Qed.

Lemma pd_Cbad : forall regs m (dp wr : Z) bs4,
    (1 <= dp)%Z -> (dp + 28 <= 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (dp + 4)) 4 = Some bs4 -> bytes_le_to_Z bs4 = wr -> (0 <= wr < 2 ^ 32)%Z -> ~ (1 <= wr <= 1000000)%Z ->
    getr regs 10 = Z_to_bv 64 dp ->
    exists regs', msteps SEGS (mkst regs (0x27a58 : word) m rom) (mkst regs' (0x27a6c : word) m rom)
      /\ regs_agree (fun r => In r [9; 13; 14]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_Cbad fx v15_reloc v15_code_vl rom). Qed.

Lemma pd_D : forall regs m (dp hr : Z) bs8,
    (1 <= dp)%Z -> (dp + 28 <= 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (dp + 8)) 4 = Some bs8 -> bytes_le_to_Z bs8 = hr -> (1 <= hr <= 1000000)%Z ->
    getr regs 10 = Z_to_bv 64 dp -> getr regs 13 = Z_to_bv 64 18446744073708551615 ->
    exists regs', msteps SEGS (mkst regs (0x27ae8 : word) m rom) (mkst regs' (0x27b1c : word) m rom)
      /\ getr regs' 18 = Z_to_bv 64 hr /\ regs_agree (fun r => In r [18; 14]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_D fx v15_reloc v15_code_vl rom). Qed.

Lemma pd_Dbad : forall regs m (dp hr : Z) bs8,
    (1 <= dp)%Z -> (dp + 28 <= 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (dp + 8)) 4 = Some bs8 -> bytes_le_to_Z bs8 = hr -> (0 <= hr < 2 ^ 32)%Z -> ~ (1 <= hr <= 1000000)%Z ->
    getr regs 10 = Z_to_bv 64 dp -> getr regs 13 = Z_to_bv 64 18446744073708551615 ->
    exists regs', msteps SEGS (mkst regs (0x27ae8 : word) m rom) (mkst regs' (0x27af4 : word) m rom)
      /\ regs_agree (fun r => In r [18; 14]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_Dbad fx v15_reloc v15_code_vl rom). Qed.

Lemma pd_E : forall regs m (wr hr : Z),
    (1 <= wr <= 1000000)%Z -> (1 <= hr <= 1000000)%Z -> (wr * hr <= 400000000)%Z ->
    getr regs 9 = Z_to_bv 64 wr -> getr regs 18 = Z_to_bv 64 hr ->
    exists regs', msteps SEGS (mkst regs (0x27b1c : word) m rom) (mkst regs' (0x27b54 : word) m rom)
      /\ regs_agree (fun r => In r [13; 14]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_E fx v15_reloc v15_code_vl rom). Qed.

Lemma pd_Ebad : forall regs m (wr hr : Z),
    (1 <= wr <= 1000000)%Z -> (1 <= hr <= 1000000)%Z -> (400000000 < wr * hr)%Z ->
    getr regs 9 = Z_to_bv 64 wr -> getr regs 18 = Z_to_bv 64 hr ->
    exists regs', msteps SEGS (mkst regs (0x27b1c : word) m rom) (mkst regs' (0x27b2c : word) m rom)
      /\ regs_agree (fun r => In r [13; 14]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_Ebad fx v15_reloc v15_code_vl rom). Qed.

Definition et_leaves : list (Z * Z) :=
    [(0x27a94, 0x10d1c); (0x27a6c, 0x11211); (0x27af4, 0x1043a); (0x27b2c, 0x103ae); (0x27c64, 0x10df9); (0x27c8c, 0x10739)]%Z.
Lemma pd_ET : forall pc msg regs m,
    In (pc, msg) et_leaves ->
    rdn SEGS m (Z_to_bv 64 0x341f8) 8 = Some (Z_to_le_bytes 8 0x35268) -> rdn SEGS m (Z_to_bv 64 0x35268) 4 = Some (Z_to_le_bytes 4 3) ->
    exists regs', msteps SEGS (mkst regs (Z_to_bv 64 pc) m rom) (mkst regs' (0x27ab8 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 msg /\ getr regs' 11 = Z_to_bv 64 0x10a51
      /\ regs_agree (fun r => In r [10; 11]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_ET fx v15_reloc v15_code_vl v15_sites_vl rom). Qed.

Definition ej_leaves : list (Z * Z) := [(0x27cec, 0x10eed); (0x27d24, 0x1152a); (0x27db0, 0x1058d)]%Z.
Lemma pd_EJ : forall pc msg regs m,
    In (pc, msg) ej_leaves ->
    rdn SEGS m (Z_to_bv 64 0x341f8) 8 = Some (Z_to_le_bytes 8 0x35268) -> rdn SEGS m (Z_to_bv 64 0x35268) 4 = Some (Z_to_le_bytes 4 3) ->
    exists regs', msteps SEGS (mkst regs (Z_to_bv 64 pc) m rom) (mkst regs' (0x155bc : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 msg /\ getr regs' 11 = Z_to_bv 64 0x10a51 /\ getr regs' 12 = Z_to_bv 64 0 /\ getr regs' 1 = Z_to_bv 64 0x27ddc
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_EJ fx v15_reloc v15_code_vl v15_sites_vl rom). Qed.

Definition pd_cells (m : word -> option byte) (s : Z) (ret : word) (sv : nat -> word) : Prop :=
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) /\
    rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (sv 8%nat)) /\
    rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (sv 9%nat)) /\
    rdn SEGS m (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 (sv 18%nat)) /\
    rdn SEGS m (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 (sv 19%nat)) /\
    rdn SEGS m (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 (sv 20%nat)) /\
    rdn SEGS m (Z_to_bv 64 (s - 56)) 8 = Some (word_to_le_bytes 8 (sv 21%nat)) /\
    rdn SEGS m (Z_to_bv 64 (s - 64)) 8 = Some (word_to_le_bytes 8 (sv 22%nat)) /\
    rdn SEGS m (Z_to_bv 64 (s - 72)) 8 = Some (word_to_le_bytes 8 (sv 23%nat)).
Lemma pd_X50 : forall regs m (s : Z) (ret : word) (sv : nat -> word),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> pd_cells m s ret sv -> getr regs 2 = Z_to_bv 64 (s - 96) ->
    exists regs', msteps SEGS (mkst regs (0x27ab8 : word) m rom) (mkst regs' (0x155bc : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 12 = Z_to_bv 64 0
      /\ getr regs' 8 = sv 8%nat /\ getr regs' 9 = sv 9%nat /\ getr regs' 18 = sv 18%nat /\ getr regs' 19 = sv 19%nat
      /\ getr regs' 20 = sv 20%nat /\ getr regs' 21 = sv 21%nat /\ getr regs' 22 = sv 22%nat /\ getr regs' 23 = sv 23%nat
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 12; 18; 19; 20; 21; 22; 23]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_X50 fx v15_reloc v15_code_vl v15_sites_vl rom). Qed.

Lemma pd_RET : forall regs m (s : Z) (ret : word) (sv : nat -> word),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret -> pd_cells m s ret sv -> getr regs 2 = Z_to_bv 64 (s - 96) ->
    exists regs', msteps SEGS (mkst regs (0x27de4 : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret
      /\ getr regs' 8 = sv 8%nat /\ getr regs' 9 = sv 9%nat /\ getr regs' 18 = sv 18%nat /\ getr regs' 19 = sv 19%nat
      /\ getr regs' 20 = sv 20%nat /\ getr regs' 21 = sv 21%nat /\ getr regs' 22 = sv 22%nat /\ getr regs' 23 = sv 23%nat
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 18; 19; 20; 21; 22; 23]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_RET fx v15_reloc v15_code_vl rom). Qed.

Lemma pd_R0 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x27de0 : word) m rom) (mkst regs' (0x27de4 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 0 /\ regs_agree (fun r => In r [10]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_R0 fx v15_reloc v15_code_vl rom). Qed.

Lemma pd_J34 : forall regs m, exists regs', msteps SEGS (mkst regs (0x27994 : word) m rom) (mkst regs' (0x27de0 : word) m rom) /\ regs_agree (fun r => False) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_J34 fx v15_reloc v15_code_vl rom). Qed.

Lemma pd_J88 : forall regs m, exists regs', msteps SEGS (mkst regs (0x27ce8 : word) m rom) (mkst regs' (0x27de0 : word) m rom) /\ regs_agree (fun r => False) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_J88 fx v15_reloc v15_code_vl rom). Qed.

Lemma pd_J7c : forall regs m, exists regs', msteps SEGS (mkst regs (0x27ddc : word) m rom) (mkst regs' (0x27de4 : word) m rom) /\ regs_agree (fun r => False) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_J7c fx v15_reloc v15_code_vl rom). Qed.

End Segs.

End DeserA.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).      (* [comment removed for export] *)
End V15LeptDeserA.

From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.VL Require LeptDeserB.
Module V15LeptDeserB.
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
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptRoom.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Reloc.Reloc.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.RelocLept.
Import V15Kit.
(* [comment removed for export] *)










Import V15CL7a.V15LeptErr.





Import V15Kit.V15Reloc. Import V15Kit.V15RelocCode. Import V15Kit.V15RelocSites. Import V15Kit.V15RelocImg. Import V15Kit.V15RelocVL.
Import V15Kit.V15RelocMusl. Import V15Kit.V15LeptEnv.
Import V15CL7a.V15LeptG.
Import ListNotations.
Open Scope bv_scope.

Section DeserB.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V15Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
Section Segs.
Variable rom : word -> option byte.
Lemma pd_F : forall regs m (dp nb ncr q dr wr hr : Z) bs20 bs12,
    (1 <= dp)%Z -> (dp + 28 <= 2 ^ 64)%Z -> (28 <= nb < 2 ^ 31)%Z -> q = (nb / 4)%Z ->
    rdn SEGS m (Z_to_bv 64 (dp + 20)) 4 = Some bs20 -> bytes_le_to_Z bs20 = ncr -> (0 <= ncr <= 256)%Z -> (ncr + 7 < q)%Z ->
    rdn SEGS m (Z_to_bv 64 (dp + 12)) 4 = Some bs12 -> bytes_le_to_Z bs12 = dr -> (0 <= dr < 2 ^ 32)%Z ->
    (0 <= wr < 2 ^ 64)%Z -> (0 <= hr < 2 ^ 64)%Z ->
    getr regs 10 = Z_to_bv 64 dp -> getr regs 11 = Z_to_bv 64 nb -> getr regs 12 = Z_to_bv 64 (dp + 20) ->
    getr regs 9 = Z_to_bv 64 wr -> getr regs 18 = Z_to_bv 64 hr ->
    exists regs', msteps SEGS (mkst regs (0x27b54 : word) m rom) (mkst regs' (0x16d34 : word) m rom)
      /\ getr regs' 22 = Z_to_bv 64 ncr /\ getr regs' 20 = Z_to_bv 64 nb /\ getr regs' 23 = Z_to_bv 64 dp
      /\ getr regs' 19 = Z_to_bv 64 (zx (sw32 dr))
      /\ getr regs' 10 = Z_to_bv 64 wr /\ getr regs' 11 = Z_to_bv 64 hr /\ getr regs' 12 = Z_to_bv 64 (zx (sw32 dr)) /\ getr regs' 1 = Z_to_bv 64 0x27b88
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 19; 20; 22; 23]%list) regs regs'.
Proof. rl_tail (@LeptDeserB.pd_F fx v15_reloc v15_code_vl v15_sites_vl rom). Qed.

Lemma pd_Fbad : forall regs m (dp nb ncr q : Z) bs20,
    (1 <= dp)%Z -> (dp + 28 <= 2 ^ 64)%Z -> (28 <= nb < 2 ^ 31)%Z -> q = (nb / 4)%Z ->
    rdn SEGS m (Z_to_bv 64 (dp + 20)) 4 = Some bs20 -> bytes_le_to_Z bs20 = ncr -> (0 <= ncr < 2 ^ 32)%Z -> ~ (ncr <= 256 /\ ncr + 7 < q)%Z ->
    getr regs 10 = Z_to_bv 64 dp -> getr regs 11 = Z_to_bv 64 nb -> getr regs 12 = Z_to_bv 64 (dp + 20) ->
    exists regs', msteps SEGS (mkst regs (0x27b54 : word) m rom) (mkst regs' (0x27c64 : word) m rom)
      /\ regs_agree (fun r => In r [12; 13; 22]%list) regs regs'.
Proof. rl_tail (@LeptDeserB.pd_Fbad fx v15_reloc v15_code_vl rom). Qed.

Lemma pd_G0 : forall regs m (s : Z),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 96)) 96 = true ->
    getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs', msteps SEGS (mkst regs (0x27b88 : word) m rom)
                              (mkst regs' (0x27c8c : word) (wbytes m (Z_to_bv 64 (s - 88)) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ regs_agree (fun r => False) regs regs'.
Proof. rl_tail (@LeptDeserB.pd_G0 fx v15_reloc v15_code_vl rom). Qed.

Lemma pd_G : forall regs m (s dp nb nc pix1 wpl hr ir : Z) (v1 : pixv) bsi,
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 96)) 96 = true ->
    PIXat m pix1 v1 -> (4096 <= pix1)%Z -> (pix1 + 64 <= s - 96)%Z -> (pix1 mod 8 = 0)%Z -> p_wpl v1 = wpl ->
    (1 <= hr <= 1000000)%Z -> (0 <= wpl)%Z -> (4 * (wpl * hr) <= 67108864)%Z ->
    (0 <= nc <= 256)%Z -> (28 <= nb < 2 ^ 31)%Z -> (4 * nc + 32 <= nb)%Z -> (1 <= dp)%Z -> (dp + nb <= s - 96)%Z -> (dp mod 4 = 0)%Z ->
    rdn SEGS m (Z_to_bv 64 (dp + 4 * nc + 24)) 4 = Some bsi -> bytes_le_to_Z bsi = ir -> (0 <= ir < 2 ^ 32)%Z ->
    getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 10 = Z_to_bv 64 pix1 -> getr regs 22 = Z_to_bv 64 nc -> getr regs 20 = Z_to_bv 64 nb ->
    getr regs 23 = Z_to_bv 64 dp -> getr regs 18 = Z_to_bv 64 hr ->
    exists regs', msteps SEGS (mkst regs (0x27b88 : word) m rom)
                              (mkst regs' (0x170a4 : word) (wbytes m (Z_to_bv 64 (s - 88)) (word_to_le_bytes 8 (Z_to_bv 64 pix1))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 96) /\ getr regs' 10 = Z_to_bv 64 (s - 88) /\ getr regs' 1 = Z_to_bv 64 0x27bdc
      /\ getr regs' 20 = Z_to_bv 64 (zx (sw32 ir))
      /\ getr regs' 8 = Z_to_bv 64 (4 * (wpl * hr)) /\ getr regs' 21 = Z_to_bv 64 (nb - 4 * nc - 28)
      /\ regs_agree (fun r => In r [1; 8; 10; 11; 12; 13; 20; 21]%list) regs regs'.
Proof. rl_tail (@LeptDeserB.pd_G fx v15_reloc v15_code_vl v15_sites_vl rom). Qed.

Lemma pd_H : forall regs m (sz wr hr d : Z),
    (0 <= sz < 2 ^ 32)%Z ->
    getr regs 8 = Z_to_bv 64 sz -> getr regs 21 = Z_to_bv 64 sz -> getr regs 20 = Z_to_bv 64 sz ->
    getr regs 9 = Z_to_bv 64 wr -> getr regs 18 = Z_to_bv 64 hr -> getr regs 19 = Z_to_bv 64 d ->
    exists regs', msteps SEGS (mkst regs (0x27bdc : word) m rom) (mkst regs' (0x16b48 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 wr /\ getr regs' 11 = Z_to_bv 64 hr /\ getr regs' 12 = Z_to_bv 64 d /\ getr regs' 1 = Z_to_bv 64 0x27bf4
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
Proof. rl_tail (@LeptDeserB.pd_H fx v15_reloc v15_code_vl v15_sites_vl rom). Qed.

Lemma pd_Hbad : forall regs m (sz msz isz : Z),
    (0 <= sz < 2 ^ 32)%Z -> (0 <= msz < 2 ^ 32)%Z -> (0 <= isz < 2 ^ 64)%Z -> (sz <> msz \/ sz <> isz) ->
    rdn SEGS m (Z_to_bv 64 0x341f8) 8 = Some (Z_to_le_bytes 8 0x35268) -> rdn SEGS m (Z_to_bv 64 0x35268) 4 = Some (Z_to_le_bytes 4 3) ->
    getr regs 8 = Z_to_bv 64 sz -> getr regs 21 = Z_to_bv 64 msz -> getr regs 20 = Z_to_bv 64 isz ->
    exists regs', msteps SEGS (mkst regs (0x27bdc : word) m rom) (mkst regs' (0x15520 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 0x108c1 /\ getr regs' 11 = Z_to_bv 64 0x10a51 /\ getr regs' 1 = Z_to_bv 64 0x27ce8
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14]%list) regs regs'.
Proof. rl_tail (@LeptDeserB.pd_Hbad fx v15_reloc v15_code_vl v15_sites_vl rom). Qed.

Lemma pd_I0 : forall regs m (s : Z),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 96)) 96 = true ->
    getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs', msteps SEGS (mkst regs (0x27bf4 : word) m rom)
                              (mkst regs' (0x27cec : word) (wbytes m (Z_to_bv 64 (s - 96)) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ regs_agree (fun r => False) regs regs'.
Proof. rl_tail (@LeptDeserB.pd_I0 fx v15_reloc v15_code_vl rom). Qed.

Lemma pd_I1 : forall regs m (s pixd : Z),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 96)) 96 = true -> (1 <= pixd < 2 ^ 64)%Z ->
    getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 10 = Z_to_bv 64 pixd -> getr regs 22 = Z_to_bv 64 0 ->
    exists regs', msteps SEGS (mkst regs (0x27bf4 : word) m rom)
                              (mkst regs' (0x27d50 : word) (wbytes m (Z_to_bv 64 (s - 96)) (word_to_le_bytes 8 (Z_to_bv 64 pixd))) rom)
      /\ getr regs' 9 = Z_to_bv 64 0 /\ getr regs' 18 = Z_to_bv 64 0 /\ getr regs' 10 = Z_to_bv 64 pixd
      /\ regs_agree (fun r => In r [9; 18]%list) regs regs'.
Proof. rl_tail (@LeptDeserB.pd_I1 fx v15_reloc v15_code_vl rom). Qed.

Lemma pd_I2 : forall regs m (s pixd dp nc : Z),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 96)) 96 = true -> (1 <= pixd < 2 ^ 64)%Z -> (1 <= nc <= 256)%Z ->
    (0 <= dp)%Z -> (dp + 28 <= 2 ^ 64)%Z ->
    getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 10 = Z_to_bv 64 pixd -> getr regs 22 = Z_to_bv 64 nc -> getr regs 23 = Z_to_bv 64 dp ->
    exists regs', msteps SEGS (mkst regs (0x27bf4 : word) m rom)
                              (mkst regs' (0x198b4 : word) (wbytes m (Z_to_bv 64 (s - 96)) (word_to_le_bytes 8 (Z_to_bv 64 pixd))) rom)
      /\ getr regs' 10 = Z_to_bv 64 (dp + 24) /\ getr regs' 11 = Z_to_bv 64 4 /\ getr regs' 12 = Z_to_bv 64 nc /\ getr regs' 1 = Z_to_bv 64 0x27c1c
      /\ getr regs' 18 = Z_to_bv 64 nc
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 18]%list) regs regs'.
Proof. rl_tail (@LeptDeserB.pd_I2 fx v15_reloc v15_code_vl v15_sites_vl rom). Qed.

Lemma pd_J0 : forall regs m (s : Z),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs', msteps SEGS (mkst regs (0x27c1c : word) m rom) (mkst regs' (0x170a4 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 (s - 96) /\ getr regs' 1 = Z_to_bv 64 0x27d24 /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
Proof. rl_tail (@LeptDeserB.pd_J0 fx v15_reloc v15_code_vl v15_sites_vl rom). Qed.

Lemma pd_J1 : forall regs m (s cm pixd : Z),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= cm < 2 ^ 64)%Z -> (0 <= pixd < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 96)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 pixd)) ->
    getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 10 = Z_to_bv 64 cm ->
    exists regs', msteps SEGS (mkst regs (0x27c1c : word) m rom) (mkst regs' (0x176bc : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 cm /\ getr regs' 9 = Z_to_bv 64 cm /\ getr regs' 1 = Z_to_bv 64 0x27c30
      /\ regs_agree (fun r => In r [1; 9; 10; 11]%list) regs regs'.
Proof. rl_tail (@LeptDeserB.pd_J1 fx v15_reloc v15_code_vl v15_sites_vl rom). Qed.

Lemma pd_K : forall regs m (s pixd : Z),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= pixd < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 96)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 pixd)) ->
    getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs', msteps SEGS (mkst regs (0x27c30 : word) m rom) (mkst regs' (0x27d50 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 pixd /\ regs_agree (fun r => In r [10]%list) regs regs'.
Proof. rl_tail (@LeptDeserB.pd_K fx v15_reloc v15_code_vl rom). Qed.

Lemma pd_GD : forall regs m (pixd dp nc sz : Z) (v : pixv),
    PIXat m pixd v -> (4096 <= pixd)%Z -> (pixd mod 8 = 0)%Z -> (0 <= nc <= 256)%Z -> (0 <= dp)%Z -> (dp + 4 * nc + 28 < 2 ^ 64)%Z ->
    (dp mod 4 = 0)%Z -> (p_data v mod 4 = 0)%Z ->
    getr regs 10 = Z_to_bv 64 pixd -> getr regs 23 = Z_to_bv 64 dp -> getr regs 18 = Z_to_bv 64 nc -> getr regs 8 = Z_to_bv 64 sz ->
    exists regs', msteps SEGS (mkst regs (0x27d50 : word) m rom) (mkst regs' (0x326c4 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 (p_data v) /\ getr regs' 11 = Z_to_bv 64 (dp + 4 * nc + 28) /\ getr regs' 12 = Z_to_bv 64 sz /\ getr regs' 1 = Z_to_bv 64 0x27d84
      /\ getr regs' 18 = Z_to_bv 64 (4 * nc)
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 18]%list) regs regs'.
Proof. rl_tail (@LeptDeserB.pd_GD fx v15_reloc v15_code_vl v15_sites_vl rom). Qed.

Lemma pd_L0 : forall regs m (s pixd : Z),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= pixd < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 96)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 pixd)) ->
    getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 22 = Z_to_bv 64 0 ->
    exists regs', msteps SEGS (mkst regs (0x27d84 : word) m rom) (mkst regs' (0x27de4 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 pixd /\ regs_agree (fun r => In r [10]%list) regs regs'.
Proof. rl_tail (@LeptDeserB.pd_L0 fx v15_reloc v15_code_vl rom). Qed.

Lemma pd_L1 : forall regs m (s pixd nc cm : Z),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= pixd < 2 ^ 64)%Z -> (1 <= nc <= 256)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 96)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 pixd)) ->
    getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 22 = Z_to_bv 64 nc -> getr regs 9 = Z_to_bv 64 cm ->
    exists regs', msteps SEGS (mkst regs (0x27d84 : word) m rom) (mkst regs' (0x18888 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 cm /\ getr regs' 11 = Z_to_bv 64 pixd /\ getr regs' 12 = Z_to_bv 64 (s - 76) /\ getr regs' 1 = Z_to_bv 64 0x27d98
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
Proof. rl_tail (@LeptDeserB.pd_L1 fx v15_reloc v15_code_vl v15_sites_vl rom). Qed.

Lemma pd_M1 : forall regs m (s pixd : Z),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= pixd < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 76)) 4 = Some (Z_to_le_bytes 4 1) ->
    rdn SEGS m (Z_to_bv 64 (s - 96)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 pixd)) ->
    getr regs 2 = Z_to_bv 64 (s - 96) ->
    exists regs', msteps SEGS (mkst regs (0x27d98 : word) m rom) (mkst regs' (0x27de4 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 pixd /\ regs_agree (fun r => In r [10]%list) regs regs'.
Proof. rl_tail (@LeptDeserB.pd_M1 fx v15_reloc v15_code_vl rom). Qed.

Lemma pd_M0 : forall regs m (s : Z),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 76)) 4 = Some (Z_to_le_bytes 4 0) ->
    getr regs 2 = Z_to_bv 64 (s - 96) ->
    exists regs', msteps SEGS (mkst regs (0x27d98 : word) m rom) (mkst regs' (0x170a4 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 (s - 96) /\ getr regs' 1 = Z_to_bv 64 0x27db0 /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
Proof. rl_tail (@LeptDeserB.pd_M0 fx v15_reloc v15_code_vl v15_sites_vl rom). Qed.

End Segs.

End DeserB.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).      (* [comment removed for export] *)
End V15LeptDeserB.

From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require FPSteps.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require FPStepsV.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require Amb.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require SymExec2.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require SymExec2Sound.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require SymRun.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require SymDrive.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptExec.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptExecW.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptExecFP.
Module V15LeptGqArms.
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
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.MemSplit.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.FPSteps.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.FPStepsV.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocBase.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocSure.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.Amb.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymExec2.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymExec2Sound.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymRun.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymDrive.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.WalksLib.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptDefs.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptStructs.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptRoom.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptExec.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptExecW.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptExecFP.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15LeptBase.
Import V15CL7a.
(* [comment removed for export] *)










Import V15CL7a.V15LeptErr.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Chain.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V15Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
(* [comment removed for export] *)
#[local] Existing Instance exf_fxd | 100.

Definition GQ_ARM_STACK : Z := 160 + 16 + LSF.
Definition STOPS : list Z := [87484]%Z.
Definition FDEF : list (nat * nat) := [(8%nat, 33%nat); (9%nat, 34%nat); (18%nat, 35%nat)].     (* [comment removed for export] *)
Definition ex_rf18 : reg := 18%bv.
Definition PC_RETERR : word := 87484%bv.
Lemma PC_RETERR_eq : Z_to_bv 64 87484 = PC_RETERR. Proof. apply bv_eq; reflexivity. Qed.
Lemma str_102c7 : str16 66247 16. Proof. str16_tac. Qed.   (* [comment removed for export] *)
Lemma str_10c63 : str16 68707 15. Proof. str16_tac. Qed.   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma F1_null_W : forall (fx : FPState) C A m md regs (s : Z) (ret : word) (S : TSet),
  frm_zero (@fp_csr fx) -> Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + GQ_ARM_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 10 = Z_to_bv 64 0 ->
  (forall (fx' : FPState) m' regs', frm_zero (@fp_csr fx') -> W C A m' md -> cs_kept regs regs' -> POSTM C A s m m' -> getr regs' 10 = Z_to_bv 64 0 ->
     realizes SEGS (mkCfg (@mkst fx' regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (Z_to_bv 64 116080) m al_rom) md) S.
Proof.
  intros fx C A0 m0 md r0 s ret S FZ CK HW0 H2 Hs16 HloA Hhi H1 Hret H10 HC.
  unfold GQ_ARM_STACK, LSF in *.
  assert (Hlo : (c_top C - LSTK + 160 <= s)%Z) by lia.
  assert (HRA : ex_keep (getr r0 ex_r1 = ret)) by exact H1.
  assert (HSP : ex_keep (getr r0 ex_r2 = Z_to_bv 64 s)) by exact H2.
  destruct fx as [fr cs]. cbn [fp_csr] in FZ.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img ll_ro LLU16] in *. pose proof LSTK_val as LV.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof (POSTM_refl C A0 s m0) as PM0. pose proof (sub_live_refl A0) as SUB0.
  rewrite <- (with_vmmaps_same md) in HW0 |- *. set (vm0 := m_vmmaps md) in *.
  pose (valsI := @nil word).
  assert (GLO1 : (c_top C - LSTK <= s - 160)%Z) by lia.
  assert (GLO2 : (s - 160 + Z.of_nat (Z.to_nat 160) <= c_top C)%Z) by (rewrite Z2Nat.id by lia; lia).
  assert (RS : (0 <= s < 2 ^ 64)%Z) by lia.
  assert (RS2 : (160 <= s)%Z) by lia.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A0 m0 _ (s - 160) (Z.to_nat 160) CK HW0 GLO1 GLO2) as SOK0.
  pose proof (exW_canary_ok SEGS 415784 m0 (canary_any m0)) as CANOK0.
  pose (vals0 := valsI ++ map (getr r0) ex_regs_list ++ map (Z_to_bv 64) [s; bv_unsigned (reg_get fr ex_r8); bv_unsigned (reg_get fr ex_r9); bv_unsigned (reg_get fr ex_rf18); exW_canary SEGS 415784 m0]).
  pose proof (exW_kn_fixed SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); bv_unsigned (reg_get fr ex_r9); bv_unsigned (reg_get fr ex_rf18); exW_canary SEGS 415784 m0]) (EVar 36) (EVar 32) (exW_canary SEGS 415784 m0) s 160 415784 65536 212992 213416 213568 213416 213568
                HW0 eq_refl (proj1 CANOK0) (proj2 CANOK0) eq_refl eq_refl eq_refl SOK0 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf0.
  pose proof (exW_kn_clr SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); bv_unsigned (reg_get fr ex_r9); bv_unsigned (reg_get fr ex_rf18); exW_canary SEGS 415784 m0]) 217704 217712 217704 217712 HW0 ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKx0_0.
  assert (HKn0 : know_ok SEGS (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); bv_unsigned (reg_get fr ex_r9); bv_unsigned (reg_get fr ex_rf18); exW_canary SEGS 415784 m0]) m0 [KRange (EVar 32) 430240 (2 ^ 63); KAlign (EVar 32) 16]).
  { ex_know r0. }
  pose proof (proj2 (Forall_app _ _ _) (conj HKn0 (proj2 (Forall_app _ _ _) (conj HKx0_0 HKf0)))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  ex_entryL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); bv_unsigned (reg_get fr ex_r9); bv_unsigned (reg_get fr ex_rf18); exW_canary SEGS 415784 m0] HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN0 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKn0 HKx0_0 HKf0 SOK0 CANOK0.
  repeat match goal with H : getr r0 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc0 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E0 := EEx) in HR, Hlf, HK, Hms |- *; set (log0 := LLx) in Hms, Hlf; set (M0 := mem_denot E0 m0 log0) in Hms end.
  assert (WP0 : W C A0 M0 (with_vmmaps vm0 md) /\ POSTM C A0 s m0 M0).
  { subst M0. apply (exW_win_blks C A0 A0 m0 _ E0 log0 (EVar 32) s 160 [] CK HW0 SUB0 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP0 as [HWs0 PMs0].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log0 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC0 : carry log0 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc0 : know_ok SEGS E0 M0 kn1) by (apply (carry_after SEGS E0 m0 log0 kn0 [] kn1 scs hs HC0 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW0)) | exact (mp_lazy _ (w_pure _ _ _ _ HW0)) | exact Hms |].
  pose (BS0 := [(32%nat, s)]).
  exW_regfactB BS0 HR ex_r10 Q10_0. exW_regfactB BS0 HR ex_r11 Q11_0. exW_regfactB BS0 HR ex_r12 Q12_0. exW_regfactB BS0 HR ex_r2 Q2_0.
  clear BS0.
  (* [comment removed for export] *)
  exW_regfactW r0 HR ex_r1 G1w.
  assert (CS0 : cs_kept r0 Rc0).
  { lazymatch type of HR with regs_ok ?EE ?sr _ => apply (exW_cs_of_sr EE sr r0 Rc0 [(2%nat, EVar 32)] HR); [exW_entry_vars | constructor; [symmetry; exact HSP | constructor] | vm_compute; reflexivity] end. }
  rewrite PC_RETERR_eq.
  lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (returnErrorPtr_W (fx := fxk) C A0 M0 _ Rc0 s 66247 68707 16 15 ret (Z_to_bv 64 0) S CK HWs0 Q2_0
             Hs16 ltac:(unfold LSF; lia) Hhi (eq_trans G1w HRA) Hret Q10_0 Q11_0 Q12_0 str_102c7 str_10c63) end.
  intros m1 r1 HW1 OUT GRW CSx A10.
  assert (PMK : POSTM C A0 s m0 m1).
  { eapply POSTM_trans; [exact PM0|]. eapply POSTM_trans; [exact PMs0|].
    apply (POSTM_range C A0 M0 _ m1 (s - (16 + LSF)) s s CK HWs0 OUT); unfold LSF; lia. }
  assert (CSK : cs_kept r0 r1) by (intros r Hr; rewrite (CSx r Hr); exact (CS0 r Hr)).
  unfold vm0 in *. rewrite (with_vmmaps_same md) in *.
  lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ => exact (HC fxk m1 r1 FZ HW1 CSK PMK A10) end.
Qed.
Lemma str_113b2 : str16 70578 17. Proof. str16_tac. Qed.   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma F2_null_W : forall (fx : FPState) C A m md regs (s : Z) (ret : word) (S : TSet),
  frm_zero (@fp_csr fx) -> Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + GQ_ARM_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 10 = Z_to_bv 64 0 ->
  (forall (fx' : FPState) m' regs', frm_zero (@fp_csr fx') -> W C A m' md -> cs_kept regs regs' -> POSTM C A s m m' -> getr regs' 10 = Z_to_bv 64 0 ->
     realizes SEGS (mkCfg (@mkst fx' regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (Z_to_bv 64 112068) m al_rom) md) S.
Proof.
  intros fx C A0 m0 md r0 s ret S FZ CK HW0 H2 Hs16 HloA Hhi H1 Hret H10 HC.
  unfold GQ_ARM_STACK, LSF in *.
  assert (Hlo : (c_top C - LSTK + 160 <= s)%Z) by lia.
  assert (HRA : ex_keep (getr r0 ex_r1 = ret)) by exact H1.
  assert (HSP : ex_keep (getr r0 ex_r2 = Z_to_bv 64 s)) by exact H2.
  destruct fx as [fr cs]. cbn [fp_csr] in FZ.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img ll_ro LLU16] in *. pose proof LSTK_val as LV.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof (POSTM_refl C A0 s m0) as PM0. pose proof (sub_live_refl A0) as SUB0.
  rewrite <- (with_vmmaps_same md) in HW0 |- *. set (vm0 := m_vmmaps md) in *.
  pose (valsI := @nil word).
  assert (GLO1 : (c_top C - LSTK <= s - 160)%Z) by lia.
  assert (GLO2 : (s - 160 + Z.of_nat (Z.to_nat 160) <= c_top C)%Z) by (rewrite Z2Nat.id by lia; lia).
  assert (RS : (0 <= s < 2 ^ 64)%Z) by lia.
  assert (RS2 : (160 <= s)%Z) by lia.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A0 m0 _ (s - 160) (Z.to_nat 160) CK HW0 GLO1 GLO2) as SOK0.
  pose proof (exW_canary_ok SEGS 415784 m0 (canary_any m0)) as CANOK0.
  pose (vals0 := valsI ++ map (getr r0) ex_regs_list ++ map (Z_to_bv 64) [s; bv_unsigned (reg_get fr ex_r8); bv_unsigned (reg_get fr ex_r9); bv_unsigned (reg_get fr ex_rf18); exW_canary SEGS 415784 m0]).
  pose proof (exW_kn_fixed SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); bv_unsigned (reg_get fr ex_r9); bv_unsigned (reg_get fr ex_rf18); exW_canary SEGS 415784 m0]) (EVar 36) (EVar 32) (exW_canary SEGS 415784 m0) s 160 415784 65536 212992 213416 213568 213416 213568
                HW0 eq_refl (proj1 CANOK0) (proj2 CANOK0) eq_refl eq_refl eq_refl SOK0 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf0.
  pose proof (exW_kn_clr SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); bv_unsigned (reg_get fr ex_r9); bv_unsigned (reg_get fr ex_rf18); exW_canary SEGS 415784 m0]) 217704 217712 217704 217712 HW0 ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKx0_0.
  assert (HKn0 : know_ok SEGS (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); bv_unsigned (reg_get fr ex_r9); bv_unsigned (reg_get fr ex_rf18); exW_canary SEGS 415784 m0]) m0 [KRange (EVar 32) 430240 (2 ^ 63); KAlign (EVar 32) 16]).
  { ex_know r0. }
  pose proof (proj2 (Forall_app _ _ _) (conj HKn0 (proj2 (Forall_app _ _ _) (conj HKx0_0 HKf0)))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  ex_entryL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); bv_unsigned (reg_get fr ex_r9); bv_unsigned (reg_get fr ex_rf18); exW_canary SEGS 415784 m0] HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN0 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKn0 HKx0_0 HKf0 SOK0 CANOK0.
  repeat match goal with H : getr r0 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc0 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E0 := EEx) in HR, Hlf, HK, Hms |- *; set (log0 := LLx) in Hms, Hlf; set (M0 := mem_denot E0 m0 log0) in Hms end.
  assert (WP0 : W C A0 M0 (with_vmmaps vm0 md) /\ POSTM C A0 s m0 M0).
  { subst M0. apply (exW_win_blks C A0 A0 m0 _ E0 log0 (EVar 32) s 160 [] CK HW0 SUB0 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP0 as [HWs0 PMs0].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log0 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC0 : carry log0 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc0 : know_ok SEGS E0 M0 kn1) by (apply (carry_after SEGS E0 m0 log0 kn0 [] kn1 scs hs HC0 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW0)) | exact (mp_lazy _ (w_pure _ _ _ _ HW0)) | exact Hms |].
  pose (BS0 := [(32%nat, s)]).
  exW_regfactB BS0 HR ex_r10 Q10_0. exW_regfactB BS0 HR ex_r11 Q11_0. exW_regfactB BS0 HR ex_r12 Q12_0. exW_regfactB BS0 HR ex_r2 Q2_0.
  clear BS0.
  (* [comment removed for export] *)
  exW_regfactW r0 HR ex_r1 G1w.
  assert (CS0 : cs_kept r0 Rc0).
  { lazymatch type of HR with regs_ok ?EE ?sr _ => apply (exW_cs_of_sr EE sr r0 Rc0 [(2%nat, EVar 32)] HR); [exW_entry_vars | constructor; [symmetry; exact HSP | constructor] | vm_compute; reflexivity] end. }
  rewrite PC_RETERR_eq.
  lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (returnErrorPtr_W (fx := fxk) C A0 M0 _ Rc0 s 66247 70578 16 17 ret (Z_to_bv 64 0) S CK HWs0 Q2_0
             Hs16 ltac:(unfold LSF; lia) Hhi (eq_trans G1w HRA) Hret Q10_0 Q11_0 Q12_0 str_102c7 str_113b2) end.
  intros m1 r1 HW1 OUT GRW CSx A10.
  assert (PMK : POSTM C A0 s m0 m1).
  { eapply POSTM_trans; [exact PM0|]. eapply POSTM_trans; [exact PMs0|].
    apply (POSTM_range C A0 M0 _ m1 (s - (16 + LSF)) s s CK HWs0 OUT); unfold LSF; lia. }
  assert (CSK : cs_kept r0 r1) by (intros r Hr; rewrite (CSx r Hr); exact (CS0 r Hr)).
  unfold vm0 in *. rewrite (with_vmmaps_same md) in *.
  lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ => exact (HC fxk m1 r1 FZ HW1 CSK PMK A10) end.
Qed.
Lemma str_10424 : str16 66596 21. Proof. str16_tac. Qed.   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma F3_null_W : forall (fx : FPState) C A m md regs (s : Z) (ret : word) (S : TSet),
  frm_zero (@fp_csr fx) -> Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + GQ_ARM_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 10 = Z_to_bv 64 0 ->
  (forall (fx' : FPState) m' regs', frm_zero (@fp_csr fx') -> W C A m' md -> cs_kept regs regs' -> POSTM C A s m m' -> getr regs' 10 = Z_to_bv 64 0 ->
     realizes SEGS (mkCfg (@mkst fx' regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (Z_to_bv 64 114844) m al_rom) md) S.
Proof.
  intros fx C A0 m0 md r0 s ret S FZ CK HW0 H2 Hs16 HloA Hhi H1 Hret H10 HC.
  unfold GQ_ARM_STACK, LSF in *.
  assert (Hlo : (c_top C - LSTK + 160 <= s)%Z) by lia.
  assert (HRA : ex_keep (getr r0 ex_r1 = ret)) by exact H1.
  assert (HSP : ex_keep (getr r0 ex_r2 = Z_to_bv 64 s)) by exact H2.
  destruct fx as [fr cs]. cbn [fp_csr] in FZ.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img ll_ro LLU16] in *. pose proof LSTK_val as LV.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof (POSTM_refl C A0 s m0) as PM0. pose proof (sub_live_refl A0) as SUB0.
  rewrite <- (with_vmmaps_same md) in HW0 |- *. set (vm0 := m_vmmaps md) in *.
  pose (valsI := @nil word).
  assert (GLO1 : (c_top C - LSTK <= s - 160)%Z) by lia.
  assert (GLO2 : (s - 160 + Z.of_nat (Z.to_nat 160) <= c_top C)%Z) by (rewrite Z2Nat.id by lia; lia).
  assert (RS : (0 <= s < 2 ^ 64)%Z) by lia.
  assert (RS2 : (160 <= s)%Z) by lia.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A0 m0 _ (s - 160) (Z.to_nat 160) CK HW0 GLO1 GLO2) as SOK0.
  pose proof (exW_canary_ok SEGS 415784 m0 (canary_any m0)) as CANOK0.
  pose (vals0 := valsI ++ map (getr r0) ex_regs_list ++ map (Z_to_bv 64) [s; bv_unsigned (reg_get fr ex_r8); bv_unsigned (reg_get fr ex_r9); bv_unsigned (reg_get fr ex_rf18); exW_canary SEGS 415784 m0]).
  pose proof (exW_kn_fixed SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); bv_unsigned (reg_get fr ex_r9); bv_unsigned (reg_get fr ex_rf18); exW_canary SEGS 415784 m0]) (EVar 36) (EVar 32) (exW_canary SEGS 415784 m0) s 160 415784 65536 212992 213416 213568 213416 213568
                HW0 eq_refl (proj1 CANOK0) (proj2 CANOK0) eq_refl eq_refl eq_refl SOK0 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf0.
  pose proof (exW_kn_clr SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); bv_unsigned (reg_get fr ex_r9); bv_unsigned (reg_get fr ex_rf18); exW_canary SEGS 415784 m0]) 217704 217712 217704 217712 HW0 ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKx0_0.
  assert (HKn0 : know_ok SEGS (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); bv_unsigned (reg_get fr ex_r9); bv_unsigned (reg_get fr ex_rf18); exW_canary SEGS 415784 m0]) m0 [KRange (EVar 32) 430240 (2 ^ 63); KAlign (EVar 32) 16]).
  { ex_know r0. }
  pose proof (proj2 (Forall_app _ _ _) (conj HKn0 (proj2 (Forall_app _ _ _) (conj HKx0_0 HKf0)))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  ex_entryL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); bv_unsigned (reg_get fr ex_r9); bv_unsigned (reg_get fr ex_rf18); exW_canary SEGS 415784 m0] HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN0 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKn0 HKx0_0 HKf0 SOK0 CANOK0.
  repeat match goal with H : getr r0 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc0 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E0 := EEx) in HR, Hlf, HK, Hms |- *; set (log0 := LLx) in Hms, Hlf; set (M0 := mem_denot E0 m0 log0) in Hms end.
  assert (WP0 : W C A0 M0 (with_vmmaps vm0 md) /\ POSTM C A0 s m0 M0).
  { subst M0. apply (exW_win_blks C A0 A0 m0 _ E0 log0 (EVar 32) s 160 [] CK HW0 SUB0 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP0 as [HWs0 PMs0].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log0 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC0 : carry log0 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc0 : know_ok SEGS E0 M0 kn1) by (apply (carry_after SEGS E0 m0 log0 kn0 [] kn1 scs hs HC0 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW0)) | exact (mp_lazy _ (w_pure _ _ _ _ HW0)) | exact Hms |].
  pose (BS0 := [(32%nat, s)]).
  exW_regfactB BS0 HR ex_r10 Q10_0. exW_regfactB BS0 HR ex_r11 Q11_0. exW_regfactB BS0 HR ex_r12 Q12_0. exW_regfactB BS0 HR ex_r2 Q2_0.
  clear BS0.
  (* [comment removed for export] *)
  exW_regfactW r0 HR ex_r1 G1w.
  assert (CS0 : cs_kept r0 Rc0).
  { lazymatch type of HR with regs_ok ?EE ?sr _ => apply (exW_cs_of_sr EE sr r0 Rc0 [(2%nat, EVar 32)] HR); [exW_entry_vars | constructor; [symmetry; exact HSP | constructor] | vm_compute; reflexivity] end. }
  rewrite PC_RETERR_eq.
  lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (returnErrorPtr_W (fx := fxk) C A0 M0 _ Rc0 s 66247 66596 16 21 ret (Z_to_bv 64 0) S CK HWs0 Q2_0
             Hs16 ltac:(unfold LSF; lia) Hhi (eq_trans G1w HRA) Hret Q10_0 Q11_0 Q12_0 str_102c7 str_10424) end.
  intros m1 r1 HW1 OUT GRW CSx A10.
  assert (PMK : POSTM C A0 s m0 m1).
  { eapply POSTM_trans; [exact PM0|]. eapply POSTM_trans; [exact PMs0|].
    apply (POSTM_range C A0 M0 _ m1 (s - (16 + LSF)) s s CK HWs0 OUT); unfold LSF; lia. }
  assert (CSK : cs_kept r0 r1) by (intros r Hr; rewrite (CSx r Hr); exact (CS0 r Hr)).
  unfold vm0 in *. rewrite (with_vmmaps_same md) in *.
  lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ => exact (HC fxk m1 r1 FZ HW1 CSK PMK A10) end.
Qed.
Lemma str_10b7c : str16 68476 23. Proof. str16_tac. Qed.   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma F4_null_W : forall (fx : FPState) C A m md regs (s : Z) (ret : word) (S : TSet),
  frm_zero (@fp_csr fx) -> Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + GQ_ARM_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 10 = Z_to_bv 64 0 ->
  (forall (fx' : FPState) m' regs', frm_zero (@fp_csr fx') -> W C A m' md -> cs_kept regs regs' -> POSTM C A s m m' -> getr regs' 10 = Z_to_bv 64 0 ->
     realizes SEGS (mkCfg (@mkst fx' regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (Z_to_bv 64 123164) m al_rom) md) S.
Proof.
  intros fx C A0 m0 md r0 s ret S FZ CK HW0 H2 Hs16 HloA Hhi H1 Hret H10 HC.
  unfold GQ_ARM_STACK, LSF in *.
  assert (Hlo : (c_top C - LSTK + 160 <= s)%Z) by lia.
  assert (HRA : ex_keep (getr r0 ex_r1 = ret)) by exact H1.
  assert (HSP : ex_keep (getr r0 ex_r2 = Z_to_bv 64 s)) by exact H2.
  destruct fx as [fr cs]. cbn [fp_csr] in FZ.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img ll_ro LLU16] in *. pose proof LSTK_val as LV.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof (POSTM_refl C A0 s m0) as PM0. pose proof (sub_live_refl A0) as SUB0.
  rewrite <- (with_vmmaps_same md) in HW0 |- *. set (vm0 := m_vmmaps md) in *.
  pose (valsI := @nil word).
  assert (GLO1 : (c_top C - LSTK <= s - 160)%Z) by lia.
  assert (GLO2 : (s - 160 + Z.of_nat (Z.to_nat 160) <= c_top C)%Z) by (rewrite Z2Nat.id by lia; lia).
  assert (RS : (0 <= s < 2 ^ 64)%Z) by lia.
  assert (RS2 : (160 <= s)%Z) by lia.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A0 m0 _ (s - 160) (Z.to_nat 160) CK HW0 GLO1 GLO2) as SOK0.
  pose proof (exW_canary_ok SEGS 415784 m0 (canary_any m0)) as CANOK0.
  pose (vals0 := valsI ++ map (getr r0) ex_regs_list ++ map (Z_to_bv 64) [s; bv_unsigned (reg_get fr ex_r8); bv_unsigned (reg_get fr ex_r9); bv_unsigned (reg_get fr ex_rf18); exW_canary SEGS 415784 m0]).
  pose proof (exW_kn_fixed SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); bv_unsigned (reg_get fr ex_r9); bv_unsigned (reg_get fr ex_rf18); exW_canary SEGS 415784 m0]) (EVar 36) (EVar 32) (exW_canary SEGS 415784 m0) s 160 415784 65536 212992 213416 213568 213416 213568
                HW0 eq_refl (proj1 CANOK0) (proj2 CANOK0) eq_refl eq_refl eq_refl SOK0 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf0.
  pose proof (exW_kn_clr SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); bv_unsigned (reg_get fr ex_r9); bv_unsigned (reg_get fr ex_rf18); exW_canary SEGS 415784 m0]) 217704 217712 217704 217712 HW0 ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKx0_0.
  assert (HKn0 : know_ok SEGS (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); bv_unsigned (reg_get fr ex_r9); bv_unsigned (reg_get fr ex_rf18); exW_canary SEGS 415784 m0]) m0 [KRange (EVar 32) 430240 (2 ^ 63); KAlign (EVar 32) 16]).
  { ex_know r0. }
  pose proof (proj2 (Forall_app _ _ _) (conj HKn0 (proj2 (Forall_app _ _ _) (conj HKx0_0 HKf0)))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  ex_entryL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); bv_unsigned (reg_get fr ex_r9); bv_unsigned (reg_get fr ex_rf18); exW_canary SEGS 415784 m0] HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN0 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKn0 HKx0_0 HKf0 SOK0 CANOK0.
  repeat match goal with H : getr r0 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc0 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E0 := EEx) in HR, Hlf, HK, Hms |- *; set (log0 := LLx) in Hms, Hlf; set (M0 := mem_denot E0 m0 log0) in Hms end.
  assert (WP0 : W C A0 M0 (with_vmmaps vm0 md) /\ POSTM C A0 s m0 M0).
  { subst M0. apply (exW_win_blks C A0 A0 m0 _ E0 log0 (EVar 32) s 160 [] CK HW0 SUB0 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP0 as [HWs0 PMs0].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log0 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC0 : carry log0 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc0 : know_ok SEGS E0 M0 kn1) by (apply (carry_after SEGS E0 m0 log0 kn0 [] kn1 scs hs HC0 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW0)) | exact (mp_lazy _ (w_pure _ _ _ _ HW0)) | exact Hms |].
  pose (BS0 := [(32%nat, s)]).
  exW_regfactB BS0 HR ex_r10 Q10_0. exW_regfactB BS0 HR ex_r11 Q11_0. exW_regfactB BS0 HR ex_r12 Q12_0. exW_regfactB BS0 HR ex_r2 Q2_0.
  clear BS0.
  (* [comment removed for export] *)
  exW_regfactW r0 HR ex_r1 G1w.
  assert (CS0 : cs_kept r0 Rc0).
  { lazymatch type of HR with regs_ok ?EE ?sr _ => apply (exW_cs_of_sr EE sr r0 Rc0 [(2%nat, EVar 32)] HR); [exW_entry_vars | constructor; [symmetry; exact HSP | constructor] | vm_compute; reflexivity] end. }
  rewrite PC_RETERR_eq.
  lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (returnErrorPtr_W (fx := fxk) C A0 M0 _ Rc0 s 66247 68476 16 23 ret (Z_to_bv 64 0) S CK HWs0 Q2_0
             Hs16 ltac:(unfold LSF; lia) Hhi (eq_trans G1w HRA) Hret Q10_0 Q11_0 Q12_0 str_102c7 str_10b7c) end.
  intros m1 r1 HW1 OUT GRW CSx A10.
  assert (PMK : POSTM C A0 s m0 m1).
  { eapply POSTM_trans; [exact PM0|]. eapply POSTM_trans; [exact PMs0|].
    apply (POSTM_range C A0 M0 _ m1 (s - (16 + LSF)) s s CK HWs0 OUT); unfold LSF; lia. }
  assert (CSK : cs_kept r0 r1) by (intros r Hr; rewrite (CSx r Hr); exact (CS0 r Hr)).
  unfold vm0 in *. rewrite (with_vmmaps_same md) in *.
  lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ => exact (HC fxk m1 r1 FZ HW1 CSK PMK A10) end.
Qed.
Lemma str_11038 : str16 69688 24. Proof. str16_tac. Qed.   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma F5_null_W : forall (fx : FPState) C A m md regs (s : Z) (ret : word) (S : TSet),
  frm_zero (@fp_csr fx) -> Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + GQ_ARM_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 10 = Z_to_bv 64 0 ->
  (forall (fx' : FPState) m' regs', frm_zero (@fp_csr fx') -> W C A m' md -> cs_kept regs regs' -> POSTM C A s m m' -> getr regs' 10 = Z_to_bv 64 0 ->
     realizes SEGS (mkCfg (@mkst fx' regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (Z_to_bv 64 124628) m al_rom) md) S.
Proof.
  intros fx C A0 m0 md r0 s ret S FZ CK HW0 H2 Hs16 HloA Hhi H1 Hret H10 HC.
  unfold GQ_ARM_STACK, LSF in *.
  assert (Hlo : (c_top C - LSTK + 160 <= s)%Z) by lia.
  assert (HRA : ex_keep (getr r0 ex_r1 = ret)) by exact H1.
  assert (HSP : ex_keep (getr r0 ex_r2 = Z_to_bv 64 s)) by exact H2.
  destruct fx as [fr cs]. cbn [fp_csr] in FZ.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img ll_ro LLU16] in *. pose proof LSTK_val as LV.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof (POSTM_refl C A0 s m0) as PM0. pose proof (sub_live_refl A0) as SUB0.
  rewrite <- (with_vmmaps_same md) in HW0 |- *. set (vm0 := m_vmmaps md) in *.
  pose (valsI := @nil word).
  assert (GLO1 : (c_top C - LSTK <= s - 160)%Z) by lia.
  assert (GLO2 : (s - 160 + Z.of_nat (Z.to_nat 160) <= c_top C)%Z) by (rewrite Z2Nat.id by lia; lia).
  assert (RS : (0 <= s < 2 ^ 64)%Z) by lia.
  assert (RS2 : (160 <= s)%Z) by lia.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A0 m0 _ (s - 160) (Z.to_nat 160) CK HW0 GLO1 GLO2) as SOK0.
  pose proof (exW_canary_ok SEGS 415784 m0 (canary_any m0)) as CANOK0.
  pose (vals0 := valsI ++ map (getr r0) ex_regs_list ++ map (Z_to_bv 64) [s; bv_unsigned (reg_get fr ex_r8); bv_unsigned (reg_get fr ex_r9); bv_unsigned (reg_get fr ex_rf18); exW_canary SEGS 415784 m0]).
  pose proof (exW_kn_fixed SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); bv_unsigned (reg_get fr ex_r9); bv_unsigned (reg_get fr ex_rf18); exW_canary SEGS 415784 m0]) (EVar 36) (EVar 32) (exW_canary SEGS 415784 m0) s 160 415784 65536 212992 213416 213568 213416 213568
                HW0 eq_refl (proj1 CANOK0) (proj2 CANOK0) eq_refl eq_refl eq_refl SOK0 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf0.
  pose proof (exW_kn_clr SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); bv_unsigned (reg_get fr ex_r9); bv_unsigned (reg_get fr ex_rf18); exW_canary SEGS 415784 m0]) 217704 217712 217704 217712 HW0 ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKx0_0.
  assert (HKn0 : know_ok SEGS (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); bv_unsigned (reg_get fr ex_r9); bv_unsigned (reg_get fr ex_rf18); exW_canary SEGS 415784 m0]) m0 [KRange (EVar 32) 430240 (2 ^ 63); KAlign (EVar 32) 16]).
  { ex_know r0. }
  pose proof (proj2 (Forall_app _ _ _) (conj HKn0 (proj2 (Forall_app _ _ _) (conj HKx0_0 HKf0)))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  ex_entryL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); bv_unsigned (reg_get fr ex_r9); bv_unsigned (reg_get fr ex_rf18); exW_canary SEGS 415784 m0] HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN0 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKn0 HKx0_0 HKf0 SOK0 CANOK0.
  repeat match goal with H : getr r0 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc0 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E0 := EEx) in HR, Hlf, HK, Hms |- *; set (log0 := LLx) in Hms, Hlf; set (M0 := mem_denot E0 m0 log0) in Hms end.
  assert (WP0 : W C A0 M0 (with_vmmaps vm0 md) /\ POSTM C A0 s m0 M0).
  { subst M0. apply (exW_win_blks C A0 A0 m0 _ E0 log0 (EVar 32) s 160 [] CK HW0 SUB0 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP0 as [HWs0 PMs0].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log0 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC0 : carry log0 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc0 : know_ok SEGS E0 M0 kn1) by (apply (carry_after SEGS E0 m0 log0 kn0 [] kn1 scs hs HC0 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW0)) | exact (mp_lazy _ (w_pure _ _ _ _ HW0)) | exact Hms |].
  pose (BS0 := [(32%nat, s)]).
  exW_regfactB BS0 HR ex_r10 Q10_0. exW_regfactB BS0 HR ex_r11 Q11_0. exW_regfactB BS0 HR ex_r12 Q12_0. exW_regfactB BS0 HR ex_r2 Q2_0.
  clear BS0.
  (* [comment removed for export] *)
  exW_regfactW r0 HR ex_r1 G1w.
  assert (CS0 : cs_kept r0 Rc0).
  { lazymatch type of HR with regs_ok ?EE ?sr _ => apply (exW_cs_of_sr EE sr r0 Rc0 [(2%nat, EVar 32)] HR); [exW_entry_vars | constructor; [symmetry; exact HSP | constructor] | vm_compute; reflexivity] end. }
  rewrite PC_RETERR_eq.
  lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (returnErrorPtr_W (fx := fxk) C A0 M0 _ Rc0 s 66247 69688 16 24 ret (Z_to_bv 64 0) S CK HWs0 Q2_0
             Hs16 ltac:(unfold LSF; lia) Hhi (eq_trans G1w HRA) Hret Q10_0 Q11_0 Q12_0 str_102c7 str_11038) end.
  intros m1 r1 HW1 OUT GRW CSx A10.
  assert (PMK : POSTM C A0 s m0 m1).
  { eapply POSTM_trans; [exact PM0|]. eapply POSTM_trans; [exact PMs0|].
    apply (POSTM_range C A0 M0 _ m1 (s - (16 + LSF)) s s CK HWs0 OUT); unfold LSF; lia. }
  assert (CSK : cs_kept r0 r1) by (intros r Hr; rewrite (CSx r Hr); exact (CS0 r Hr)).
  unfold vm0 in *. rewrite (with_vmmaps_same md) in *.
  lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ => exact (HC fxk m1 r1 FZ HW1 CSK PMK A10) end.
Qed.
Lemma str_110a7 : str16 69799 19. Proof. str16_tac. Qed.   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma F6_null_W : forall (fx : FPState) C A m md regs (s : Z) (ret : word) (S : TSet),
  frm_zero (@fp_csr fx) -> Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + GQ_ARM_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 10 = Z_to_bv 64 0 ->
  (forall (fx' : FPState) m' regs', frm_zero (@fp_csr fx') -> W C A m' md -> cs_kept regs regs' -> POSTM C A s m m' -> getr regs' 10 = Z_to_bv 64 0 ->
     realizes SEGS (mkCfg (@mkst fx' regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (Z_to_bv 64 119812) m al_rom) md) S.
Proof.
  intros fx C A0 m0 md r0 s ret S FZ CK HW0 H2 Hs16 HloA Hhi H1 Hret H10 HC.
  unfold GQ_ARM_STACK, LSF in *.
  assert (Hlo : (c_top C - LSTK + 160 <= s)%Z) by lia.
  assert (HRA : ex_keep (getr r0 ex_r1 = ret)) by exact H1.
  assert (HSP : ex_keep (getr r0 ex_r2 = Z_to_bv 64 s)) by exact H2.
  destruct fx as [fr cs]. cbn [fp_csr] in FZ.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img ll_ro LLU16] in *. pose proof LSTK_val as LV.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof (POSTM_refl C A0 s m0) as PM0. pose proof (sub_live_refl A0) as SUB0.
  rewrite <- (with_vmmaps_same md) in HW0 |- *. set (vm0 := m_vmmaps md) in *.
  pose (valsI := @nil word).
  assert (GLO1 : (c_top C - LSTK <= s - 160)%Z) by lia.
  assert (GLO2 : (s - 160 + Z.of_nat (Z.to_nat 160) <= c_top C)%Z) by (rewrite Z2Nat.id by lia; lia).
  assert (RS : (0 <= s < 2 ^ 64)%Z) by lia.
  assert (RS2 : (160 <= s)%Z) by lia.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A0 m0 _ (s - 160) (Z.to_nat 160) CK HW0 GLO1 GLO2) as SOK0.
  pose proof (exW_canary_ok SEGS 415784 m0 (canary_any m0)) as CANOK0.
  pose (vals0 := valsI ++ map (getr r0) ex_regs_list ++ map (Z_to_bv 64) [s; bv_unsigned (reg_get fr ex_r8); bv_unsigned (reg_get fr ex_r9); bv_unsigned (reg_get fr ex_rf18); exW_canary SEGS 415784 m0]).
  pose proof (exW_kn_fixed SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); bv_unsigned (reg_get fr ex_r9); bv_unsigned (reg_get fr ex_rf18); exW_canary SEGS 415784 m0]) (EVar 36) (EVar 32) (exW_canary SEGS 415784 m0) s 160 415784 65536 212992 213416 213568 213416 213568
                HW0 eq_refl (proj1 CANOK0) (proj2 CANOK0) eq_refl eq_refl eq_refl SOK0 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf0.
  pose proof (exW_kn_clr SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); bv_unsigned (reg_get fr ex_r9); bv_unsigned (reg_get fr ex_rf18); exW_canary SEGS 415784 m0]) 217704 217712 217704 217712 HW0 ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKx0_0.
  assert (HKn0 : know_ok SEGS (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); bv_unsigned (reg_get fr ex_r9); bv_unsigned (reg_get fr ex_rf18); exW_canary SEGS 415784 m0]) m0 [KRange (EVar 32) 430240 (2 ^ 63); KAlign (EVar 32) 16]).
  { ex_know r0. }
  pose proof (proj2 (Forall_app _ _ _) (conj HKn0 (proj2 (Forall_app _ _ _) (conj HKx0_0 HKf0)))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  ex_entryL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); bv_unsigned (reg_get fr ex_r9); bv_unsigned (reg_get fr ex_rf18); exW_canary SEGS 415784 m0] HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN0 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKn0 HKx0_0 HKf0 SOK0 CANOK0.
  repeat match goal with H : getr r0 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc0 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E0 := EEx) in HR, Hlf, HK, Hms |- *; set (log0 := LLx) in Hms, Hlf; set (M0 := mem_denot E0 m0 log0) in Hms end.
  assert (WP0 : W C A0 M0 (with_vmmaps vm0 md) /\ POSTM C A0 s m0 M0).
  { subst M0. apply (exW_win_blks C A0 A0 m0 _ E0 log0 (EVar 32) s 160 [] CK HW0 SUB0 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP0 as [HWs0 PMs0].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log0 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC0 : carry log0 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc0 : know_ok SEGS E0 M0 kn1) by (apply (carry_after SEGS E0 m0 log0 kn0 [] kn1 scs hs HC0 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW0)) | exact (mp_lazy _ (w_pure _ _ _ _ HW0)) | exact Hms |].
  pose (BS0 := [(32%nat, s)]).
  exW_regfactB BS0 HR ex_r10 Q10_0. exW_regfactB BS0 HR ex_r11 Q11_0. exW_regfactB BS0 HR ex_r12 Q12_0. exW_regfactB BS0 HR ex_r2 Q2_0.
  clear BS0.
  (* [comment removed for export] *)
  exW_regfactW r0 HR ex_r1 G1w.
  assert (CS0 : cs_kept r0 Rc0).
  { lazymatch type of HR with regs_ok ?EE ?sr _ => apply (exW_cs_of_sr EE sr r0 Rc0 [(2%nat, EVar 32)] HR); [exW_entry_vars | constructor; [symmetry; exact HSP | constructor] | vm_compute; reflexivity] end. }
  rewrite PC_RETERR_eq.
  lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (returnErrorPtr_W (fx := fxk) C A0 M0 _ Rc0 s 66247 69799 16 19 ret (Z_to_bv 64 0) S CK HWs0 Q2_0
             Hs16 ltac:(unfold LSF; lia) Hhi (eq_trans G1w HRA) Hret Q10_0 Q11_0 Q12_0 str_102c7 str_110a7) end.
  intros m1 r1 HW1 OUT GRW CSx A10.
  assert (PMK : POSTM C A0 s m0 m1).
  { eapply POSTM_trans; [exact PM0|]. eapply POSTM_trans; [exact PMs0|].
    apply (POSTM_range C A0 M0 _ m1 (s - (16 + LSF)) s s CK HWs0 OUT); unfold LSF; lia. }
  assert (CSK : cs_kept r0 r1) by (intros r Hr; rewrite (CSx r Hr); exact (CS0 r Hr)).
  unfold vm0 in *. rewrite (with_vmmaps_same md) in *.
  lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ => exact (HC fxk m1 r1 FZ HW1 CSK PMK A10) end.
Qed.
End Chain.
End V15LeptGqArms.

From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.VL Require LeptPixHdr.
Module V15LeptPixHdr.
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
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptRoom.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Reloc.Reloc.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.RelocLept.
Import V15Kit.
(* [comment removed for export] *)










Import V15CL7a.V15LeptErr.





Import V15Kit.V15Reloc. Import V15Kit.V15RelocCode. Import V15Kit.V15RelocSites. Import V15Kit.V15RelocImg. Import V15Kit.V15RelocVL.
Import V15Kit.V15RelocMusl. Import V15Kit.V15LeptEnv.
Import V15CL7a.V15LeptG.
Import ListNotations.
Open Scope bv_scope.

Section PixHdr.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V15Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
Definition hdr_ok (w h d : Z) : Prop := dval d /\ (w <= 20000)%Z /\ (h <= 20000)%Z /\ (4 * (wpl_of w d * h) <= 67108864)%Z.
Definition pix_hdr (w h d : Z) : pixv := PIXV w h d (spp_of d) (wpl_of w d) 1 0 0 0 0 0 0 0.
Definition pix_new (C : lctx) (A A' : AS) (m' : word -> option byte) (pix : Z) (v : pixv) : Prop :=
  (4096 <= pix)%Z /\ (pix + 64 <= alloc_top (c_vm C))%Z /\ (pix mod 16 = 0)%Z /\
  live A (Z_to_bv 64 pix) = None /\ live (c_A0 C) (Z_to_bv 64 pix) = None /\ live A' (Z_to_bv 64 pix) = Some 64%Z /\
  (forall q, q <> Z_to_bv 64 pix -> live A' q = live A q) /\ PIXat m' pix v.
Theorem pixCreateHeader_W : forall C A m md regs (s w h d : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 48 + LSF <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x455c0 ->
  getr regs 10 = Z_to_bv 64 w -> getr regs 11 = Z_to_bv 64 h -> getr regs 12 = Z_to_bv 64 d ->
  (1 <= w <= 1000000)%Z -> (1 <= h <= 1000000)%Z -> (w * h <= 400000000)%Z -> (0 <= d < 2 ^ 64)%Z ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     ((getr regs' 10 = Z_to_bv 64 0 /\ forall q, live A' q = live A q)
      \/ (exists pix, getr regs' 10 = Z_to_bv 64 pix /\ (hdr_ok w h d /\ pix_new C A A' m' pix (pix_hdr w h d)))) ->
     roomtr A (m_vmmaps md) A' vm' RK_hdr RB_hdr ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x16d34 : word) m al_rom) md) S.
Proof. rl_tail (@LeptPixHdr.pixCreateHeader_W fx v15_reloc v15_code v15_sites v15_code_vl v15_sites_vl v15_lept v15_img_vl v15_data v15_img v15_rw v15_pf v15_lenv_vl AL CL ASR PINS (v15_pinsG P16)). Qed.

End PixHdr.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).      (* [comment removed for export] *)
End V15LeptPixHdr.

Module V15LeptThrErr.
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
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.MemSplit.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.FPSteps.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.FPStepsV.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocBase.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocSure.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.Amb.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymExec2.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymExec2Sound.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymRun.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymDrive.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.WalksLib.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptDefs.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptStructs.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptRoom.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptExec.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptExecW.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptExecFP.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15LeptBase.
Import V15CL7a.
(* [comment removed for export] *)










Import V15CL7a.V15LeptErr.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Chain.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V15Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
(* [comment removed for export] *)
#[local] Existing Instance exf_fxd | 100.

Definition THRE_WIN : Z := 4096.
Definition STOPS : list Z := [87484]%Z.
Definition FDEF : list (nat * nat) := [(8%nat, 33%nat)].
Definition PC_RETERR : word := 87484%bv.
Lemma PC_RETERR_eq : Z_to_bv 64 87484 = PC_RETERR. Proof. apply bv_eq; reflexivity. Qed.
Lemma str_thr_msg_d : str16 68948 14. Proof. str16_tac. Qed.
Lemma str_thr_proc : str16 69799 19. Proof. str16_tac. Qed.

Lemma thr_d_W : forall (fx : FPState) C A m md regs (s pixs w h d : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + THRE_WIN <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 10 = Z_to_bv 64 pixs ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> (0 <= pixs < 2 ^ 64)%Z -> (pixs <> 0)%Z -> (pixs mod 16 = 0)%Z ->
  (0 <= w < 2 ^ 31)%Z -> (0 <= h < 2 ^ 31)%Z -> (0 <= d < 2 ^ 31)%Z -> d <> 8%Z ->
  rdn SEGS m (Z_to_bv 64 (pixs + 0)) 4 = Some (Z_to_le_bytes 4 w) -> rdn SEGS m (Z_to_bv 64 (pixs + 4)) 4 = Some (Z_to_le_bytes 4 h) ->
  rdn SEGS m (Z_to_bv 64 (pixs + 8)) 4 = Some (Z_to_le_bytes 4 d) ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C A s m m' -> getr regs' 10 = Z_to_bv 64 0 ->
     realizes SEGS (mkCfg (@mkst fx regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (Z_to_bv 64 119812) m al_rom) md) S.
Proof.
  intros fx C A0 m0 md r0 s pixs w h d ret S CK HW0 H2 Hs16 Hlo Hhi H1 Hret H10 Lpixs_a0 Rpixs NZpixs ALpixs Rw Rh Rd NEd Cw Ch Cd HC.
  unfold THRE_WIN in *.
  assert (HRA : ex_keep (getr r0 ex_r1 = ret)) by exact H1.     (* [comment removed for export] *)
  assert (HSP : ex_keep (getr r0 ex_r2 = Z_to_bv 64 s)) by exact H2.
  destruct fx as [fr cs]. pose proof I as FZ.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img ll_ro LLU16] in *. pose proof LSTK_val as LV.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof (POSTM_refl C A0 s m0) as PM0. pose proof (sub_live_refl A0) as SUB0.
  rewrite <- (with_vmmaps_same md) in HW0 |- *. set (vm0 := m_vmmaps md) in *.
  pose (valsI := @nil word).
  assert (GLO1 : (c_top C - LSTK <= s - 4096)%Z) by lia.
  assert (GLO2 : (s - 4096 + Z.of_nat (Z.to_nat 4096) <= c_top C)%Z) by (rewrite Z2Nat.id by lia; lia).
  assert (RS : (0 <= s < 2 ^ 64)%Z) by lia.
  assert (RS2 : (4096 <= s)%Z) by lia.
  pose proof Rpixs as RRpixs.
  pose proof (exW_win_blk_apart_h C A0 m0 _ s 4096 pixs 64 CK HW0 Lpixs_a0 ltac:(lia) Rpixs ltac:(lia)) as WAPpixs.
  assert (Rpixs2 : (4096 <= pixs)%Z /\ (pixs + 64 <= alloc_top (c_vm C))%Z).
  { destruct (blk_range C A0 m0 _ (Z_to_bv 64 pixs) 64 CK HW0 Lpixs_a0 ltac:(lia)) as [G1 G2]. rewrite u_Z2bv in G1, G2 by lia. split; [exact G1 | lia]. }
  (* [comment removed for export] *)
  pose proof (W_sok_win C A0 m0 _ (s - 4096) (Z.to_nat 4096) CK HW0 GLO1 GLO2) as SOK0.
  pose proof (exW_canary_ok SEGS 415784 m0 (canary_any m0)) as CANOK0.
  pose (vals0 := valsI ++ map (getr r0) ex_regs_list ++ map (Z_to_bv 64) [s; bv_unsigned (reg_get fr ex_r8); pixs; w; h; d; exW_canary SEGS 415784 m0]).
  pose proof (exW_kn_fixed SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; w; h; d; exW_canary SEGS 415784 m0]) (EVar 38) (EVar 32) (exW_canary SEGS 415784 m0) s 4096 415784 65536 212992 213416 213568 213416 213568
                HW0 eq_refl (proj1 CANOK0) (proj2 CANOK0) eq_refl eq_refl eq_refl SOK0 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf0.
  pose proof (exW_kn_clr SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; w; h; d; exW_canary SEGS 415784 m0]) 217704 217712 217704 217712 HW0 ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKx0_0.
  assert (HKn0 : know_ok SEGS (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; w; h; d; exW_canary SEGS 415784 m0]) m0 [KRange (EVar 32) 434176 (2 ^ 63); KAlign (EVar 32) 16; KRange (EVar 34) 1 (2 ^ 47); KAlign (EVar 34) 16; KDisj (SA (EVar 32) (-4096)) 4096 (SA (EVar 34) 0) 64; KWord (SA (EVar 34) 0) 4 (EVar 35); KWord (SA (EVar 34) 4) 4 (EVar 36); KWord (SA (EVar 34) 8) 4 (EVar 37); KRange (EVar 35) 0 (2 ^ 31 - 1); KRange (EVar 36) 0 (2 ^ 31 - 1); KRange (EVar 37) 0 (2 ^ 31 - 1)]).
  { ex_know r0. }
  pose proof (proj2 (Forall_app _ _ _) (conj HKn0 (proj2 (Forall_app _ _ _) (conj HKx0_0 HKf0)))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  ex_entryL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; w; h; d; exW_canary SEGS 415784 m0] HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN0 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKn0 HKx0_0 HKf0 SOK0 CANOK0.
  repeat match goal with H : getr r0 _ = _ |- _ => clear H end.
  exb_adriveS 2000%nat 6000%nat STOPS (SCR [true] [] []) FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc0 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E0 := EEx) in HR, Hlf, HK, Hms |- *; set (log0 := LLx) in Hms, Hlf; set (M0 := mem_denot E0 m0 log0) in Hms end.
  assert (WP0 : W C A0 M0 (with_vmmaps vm0 md) /\ POSTM C A0 s m0 M0).
  { subst M0. apply (exW_win_blks C A0 A0 m0 _ E0 log0 (EVar 32) s 4096 [] CK HW0 SUB0 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP0 as [HWs0 PMs0].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log0 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC0 : carry log0 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc0 : know_ok SEGS E0 M0 kn1) by (apply (carry_after SEGS E0 m0 log0 kn0 [] kn1 scs hs HC0 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW0)) | exact (mp_lazy _ (w_pure _ _ _ _ HW0)) | exact Hms |].
  pose (BS0 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs)]).
  exW_regfactB BS0 HR ex_r10 Q10_0. exW_regfactB BS0 HR ex_r11 Q11_0. exW_regfactB BS0 HR ex_r12 Q12_0. exW_regfactB BS0 HR ex_r1 Q1_0. exW_regfactB BS0 HR ex_r2 Q2_0.
  clear BS0.
  lazymatch type of Q2_0 with _ = Z_to_bv 64 (s + ?off) => pose (OFF0 := off) end.
  (* [comment removed for export] *)
  rewrite PC_RETERR_eq.
  lazymatch type of Q1_0 with _ = Z_to_bv 64 ?ra => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (returnErrorPtr_W (fx := fxk) C A0 M0 _ Rc0 (s + OFF0) 68948 69799 14 19 (Z_to_bv 64 ra) (Z_to_bv 64 0) S CK HWs0 Q2_0
             ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF0, LSF; lia) ltac:(unfold OFF0; lia) Q1_0
             ltac:(red; apply bv_eq; reflexivity) Q10_0 Q11_0 Q12_0 str_thr_msg_d str_thr_proc) end end.
  intros m1 r1 HW1 OUT0 GRW0 CSx0 A10_0.
  pose proof CSx0 as CS0. clear CSx0.
  assert (PM1 : POSTM C A0 s m0 m1).
  { eapply POSTM_trans; [exact PM0|]. eapply POSTM_trans; [exact PMs0|].
    apply (POSTM_range C A0 M0 _ m1 (s + OFF0 - (16 + LSF)) (s + OFF0) s CK HWs0 OUT0); unfold OFF0, LSF; lia. }
  assert (KEPT0 : Forall (ex_region_kept E0 M0 m1) [(EVar 32, OFF0, 0%Z); (EVar 34, 0%Z, 64%Z)]).
  { constructor; [exact (exW_kept_out E0 M0 m1 (EVar 32) s OFF0 0 (s + OFF0 - (16 + LSF)) (s + OFF0) OUT0 eq_refl RS (or_intror (Z.le_refl _)))|]. constructor; [apply (exW_kept_out E0 M0 m1 (EVar 34) pixs 0 64 (s + OFF0 - (16 + LSF)) (s + OFF0) OUT0 eq_refl RRpixs); left; unfold OFF0, LSF; lia|]. constructor. }
  pose proof (ex_know_keepD SEGS E0 M0 m1 _ [] _ HKc0 KEPT0) as HKk0.
  match type of HKk0 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E0 m1 kk') in HKk0 end.
  pose proof (regs_ok_agree 39%nat E0 (ex_envL vals0 r1 [exW_canary SEGS 415784 m1]) _ _ (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa0.
  pose proof (exW_regs_call _ _ _ _ _ HRa0 (ex_regs_ok_junk vals0 r1 [exW_canary SEGS 415784 m1] 39%nat ltac:(vm_cast_no_check (eq_refl 39%nat))) CS0) as HRn1.
  clear HRa0.
  assert (HKa1 : know_ok SEGS (ex_envL vals0 r1 [exW_canary SEGS 415784 m1]) m1 _) by (exact (know_ok_agree SEGS 39%nat E0 _ m1 _ (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk0)).
  rewrite (fr_denot_agree 39%nat E0 (ex_envL vals0 r1 [exW_canary SEGS 415784 m1]) _ fr (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc0 HKk0 KEPT0 HC0 HWs0 PMs0 Q10_0 Q11_0 Q12_0 Q1_0 Q2_0 PM0 HW0 OUT0 GRW0 CS0 OFF0.
  subst M0. clear log0. clear E0. try clear Rc0. clear KN0.
  lazymatch type of HRn1 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn1 end.
  pose proof (ex_regs_ok_reexpr _ _ r1 ex_r10 (ELit 0) HRn1 ltac:(apply ex_reg_ne0; vm_compute; discriminate) A10_0) as HRx1. clear HRn1. rename HRx1 into HRn1.
  lazymatch type of HRn1 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn1 end.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A0 m1 _ (s - 4096) (Z.to_nat 4096) CK HW1 GLO1 GLO2) as SOK1.
  pose proof (exW_canary_ok SEGS 415784 m1 (canary_any m1)) as CANOK1.
  pose (vals1 := vals0 ++ map (getr r1) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m1]).
  pose proof (exW_kn_fixed SEGS C A0 m1 _ (ex_envL vals0 r1 [exW_canary SEGS 415784 m1]) (EVar 71) (EVar 32) (exW_canary SEGS 415784 m1) s 4096 415784 65536 212992 213416 213568 213416 213568
                HW1 eq_refl (proj1 CANOK1) (proj2 CANOK1) eq_refl eq_refl eq_refl SOK1 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf1.
  pose proof (exW_kn_clr SEGS C A0 m1 _ (ex_envL vals0 r1 [exW_canary SEGS 415784 m1]) 217704 217712 217704 217712 HW1 ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKx0_1.
  pose proof (proj2 (Forall_app _ _ _) (conj HKx0_1 (proj2 (Forall_app _ _ _) (conj HKf1 HKa1)))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn1 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN1 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKx0_1 HKf1 HKa1 SOK1 CANOK1.
  repeat match goal with H : getr r1 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_ret ST ret HRA Hret RcF HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E1 := EEx) in HR, Hlf, HK, Hms |- *; set (log1 := LLx) in Hms, Hlf; set (M1 := mem_denot E1 m1 log1) in Hms end.
  assert (WP1 : W C A0 M1 (with_vmmaps vm0 md) /\ POSTM C A0 s m1 M1).
  { subst M1. apply (exW_win_blks C A0 A0 m1 _ E1 log1 (EVar 32) s 4096 [] CK HW1 SUB0 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP1 as [HWs1 PMs1].
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact Hms |].
  pose (BSF := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs)]).
  exW_regfactB BSF HR ex_r10 G10.
  unfold vm0 in *. rewrite (with_vmmaps_same md) in *.
  apply (HC M1 RcF HWs1).
  - lazymatch type of HR with regs_ok ?EE ?sr _ => apply (exW_cs_of_sr EE sr r0 RcF [(2%nat, EVar 32)] HR); [exW_entry_vars | constructor; [symmetry; exact HSP | constructor] | vm_compute; reflexivity] end.
  - eapply POSTM_trans; [exact PM1 | exact PMs1].
  - exact G10.
Qed.
End Chain.
End V15LeptThrErr.
