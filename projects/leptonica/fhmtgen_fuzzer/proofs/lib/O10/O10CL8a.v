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
From OSSVerify.leptonica.fhmtgen_fuzzer.images Require Plain.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require PropExec.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require CatExec.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require CatSim.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require StepTac.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require Hoare.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require ShapeAlg.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require AllocIface.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require PureModel.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require VmLedger.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require StoreOk.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require MemSplit.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require RefMemcpyLib.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require StartupTac.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require WalkTac.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require AllocBase.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require AllocCalloc.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require AllocSure.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require SumWalkTac.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require SumSpecs.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require WalksLib.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require W2Lib.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require LeptDefs.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require LeptStructs.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.O10 Require O10LeptStderr.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.O10 Require O10LeptBase.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.O10 Require O10CL7a.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require LeptRoom.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc Require Reloc.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require RelocLept.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.OL Require LeptCmap.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.O10 Require O10Kit.
Module O10LeptCmap.
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
Import OSSVerify.leptonica.fhmtgen_fuzzer.images.Plain.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StepTac.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AllocIface.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PureModel.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.VmLedger.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StoreOk.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.MemSplit.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefMemcpyLib.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StartupTac.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.WalkTac.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocBase.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocSure.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.SumWalkTac.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.SumSpecs.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.WalksLib.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.W2Lib.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.LeptDefs.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.LeptStructs.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.O10.O10LeptStderr.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.O10.O10LeptBase.
Import O10CL7a.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.LeptRoom.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.Reloc.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.RelocLept.
Import O10Kit.
(* [comment removed for export] *)










Import O10CL7a.O10LeptErr.





Import O10Kit.O10Reloc. Import O10Kit.O10RelocCode. Import O10Kit.O10RelocSites. Import O10Kit.O10RelocImg. Import O10Kit.O10RelocOL.
Import O10Kit.O10RelocMusl. Import O10Kit.O10LeptEnv.
Import O10CL7a.O10LeptG.
Import ListNotations.
Open Scope bv_scope.

Lemma sllw_1 : forall d, (d = 1 \/ d = 2 \/ d = 4 \/ d = 8)%Z -> v_sllw (Z_to_bv 64 1) (Z_to_bv 64 d) = Z_to_bv 64 (2 ^ d).
Proof. rl_tail (@LeptCmap.sllw_1). Qed.

Section Cmap.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LL16} {P16 : O10Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
Theorem pixcmapDestroy_W : forall C A m md regs (s pp cm : Z) (cv : cmapv) (k : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 32 + ALLOC_STACK <= s)%Z -> (s <= pp)%Z -> (pp + 8 <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x3d100 ->
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
  realizes SEGS (mkCfg (mkst regs (0x18d04 : word) m al_rom) md) S.
Proof. rl_tail (@LeptCmap.pixcmapDestroy_W fx o10_reloc o10_code_ol o10_sites_ol o10_lept AL CL ASR PINS (o10_pinsG P16)). Qed.

End Cmap.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).      (* [comment removed for export] *)
End O10LeptCmap.

From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require LibAtomic.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require LeptArith.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require LeptArith2.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.OL Require LeptDeserA.
Module O10LeptDeserA.
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
Import OSSVerify.leptonica.fhmtgen_fuzzer.images.Plain.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StepTac.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AllocIface.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PureModel.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.VmLedger.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StoreOk.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.MemSplit.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefMemcpyLib.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StartupTac.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.WalkTac.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocBase.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocSure.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.SumWalkTac.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.SumSpecs.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.WalksLib.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.W2Lib.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.LibAtomic.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.LeptDefs.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.LeptStructs.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.LeptArith.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.LeptArith2.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.O10.O10LeptStderr.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.O10.O10LeptBase.
Import O10CL7a.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.LeptRoom.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.Reloc.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.RelocLept.
Import O10Kit.
(* [comment removed for export] *)










Import O10CL7a.O10LeptErr.





Import O10Kit.O10Reloc. Import O10Kit.O10RelocCode. Import O10Kit.O10RelocSites. Import O10Kit.O10RelocImg. Import O10Kit.O10RelocOL.
Import O10Kit.O10RelocMusl. Import O10Kit.O10LeptEnv.
Import O10CL7a.O10LeptG.
Import ListNotations.
Open Scope bv_scope.

Section DeserA.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LL16} {P16 : O10Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
Section Segs.
Variable rom : word -> option byte.
Definition FR12 (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
       (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
       (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
       (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)))
       (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr regs 18)))
       (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (getr regs 19)))
       (Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (getr regs 20)))
       (Z_to_bv 64 (s - 56)) (word_to_le_bytes 8 (getr regs 21)))
       (Z_to_bv 64 (s - 64)) (word_to_le_bytes 8 (getr regs 22)))
       (Z_to_bv 64 (s - 72)) (word_to_le_bytes 8 (getr regs 23)))
       (Z_to_bv 64 (s - 80)) (word_to_le_bytes 8 (getr regs 24)))
       (Z_to_bv 64 (s - 88)) (word_to_le_bytes 8 (getr regs 25)).
Lemma pd_A0 : forall regs m (s dp nb : Z) (ret : word),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= dp < 2 ^ 64)%Z -> (0 <= nb < 2 ^ 31)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 112)) 112 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 dp -> getr regs 11 = Z_to_bv 64 nb ->
    exists regs',
      msteps SEGS (mkst regs (0x1f944 : word) m rom) (mkst regs' (0x1f984 : word) (FR12 m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 112) /\ getr regs' 10 = Z_to_bv 64 dp /\ getr regs' 11 = Z_to_bv 64 nb
      /\ getr regs' 12 = Z_to_bv 64 18446744071562067995 /\ getr regs' 13 = Z_to_bv 64 (nb + 18446744071562067968)
      /\ regs_agree (fun r => In r [2; 12; 13]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_A0 fx o10_reloc o10_code_ol rom). Qed.

Lemma pd_A1 : forall regs m (nb : Z),
    (28 <= nb < 2 ^ 31)%Z -> getr regs 12 = Z_to_bv 64 18446744071562067995 -> getr regs 13 = Z_to_bv 64 (nb + 18446744071562067968) ->
    exists regs', msteps SEGS (mkst regs (0x1f984 : word) m rom) (mkst regs' (0x1f9e4 : word) m rom) /\ regs_agree (fun r => False) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_A1 fx o10_reloc o10_code_ol rom). Qed.

Lemma pd_A2 : forall regs m (nb : Z),
    (0 <= nb < 28)%Z -> getr regs 12 = Z_to_bv 64 18446744071562067995 -> getr regs 13 = Z_to_bv 64 (nb + 18446744071562067968) ->
    getr regs 11 = Z_to_bv 64 nb ->
    rdn SEGS m (Z_to_bv 64 0x2ba18) 8 = Some (Z_to_le_bytes 8 0x2ca88) -> rdn SEGS m (Z_to_bv 64 0x2ca88) 4 = Some (Z_to_le_bytes 4 3) ->
    exists regs',
      msteps SEGS (mkst regs (0x1f984 : word) m rom) (mkst regs' (0x156a0 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 0x10dff /\ getr regs' 11 = Z_to_bv 64 0x10bc2 /\ getr regs' 12 = Z_to_bv 64 nb /\ getr regs' 1 = Z_to_bv 64 0x1f9b8
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_A2 fx o10_reloc o10_code_ol o10_sites_ol rom). Qed.

Lemma pd_B : forall regs m (dp : Z) (b0 b1 b2 b3 : byte),
    (1 <= dp)%Z -> (dp + 4 <= 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 dp) 1 = Some [b0] -> rdn SEGS m (Z_to_bv 64 (dp + 1)) 1 = Some [b1] ->
    rdn SEGS m (Z_to_bv 64 (dp + 2)) 1 = Some [b2] -> rdn SEGS m (Z_to_bv 64 (dp + 3)) 1 = Some [b3] ->
    u b0 = 115%Z -> u b1 = 112%Z -> u b2 = 105%Z -> u b3 = 120%Z ->
    getr regs 10 = Z_to_bv 64 dp ->
    exists regs', msteps SEGS (mkst regs (0x1f9e4 : word) m rom) (mkst regs' (0x1fa14 : word) m rom)
      /\ regs_agree (fun r => In r [12; 13]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_B fx o10_reloc o10_code_ol rom). Qed.

Lemma pd_Bbad : forall regs m (dp : Z) (b0 b1 b2 b3 : byte),
    (1 <= dp)%Z -> (dp + 4 <= 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 dp) 1 = Some [b0] -> rdn SEGS m (Z_to_bv 64 (dp + 1)) 1 = Some [b1] ->
    rdn SEGS m (Z_to_bv 64 (dp + 2)) 1 = Some [b2] -> rdn SEGS m (Z_to_bv 64 (dp + 3)) 1 = Some [b3] ->
    ~ (u b0 = 115 /\ u b1 = 112 /\ u b2 = 105 /\ u b3 = 120)%Z ->
    getr regs 10 = Z_to_bv 64 dp ->
    exists regs', msteps SEGS (mkst regs (0x1f9e4 : word) m rom) (mkst regs' (0x1fa50 : word) m rom)
      /\ regs_agree (fun r => In r [12; 13]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_Bbad fx o10_reloc o10_code_ol rom). Qed.

Lemma pd_C : forall regs m (dp wr : Z) bs4,
    (1 <= dp)%Z -> (dp + 28 <= 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (dp + 4)) 4 = Some bs4 -> bytes_le_to_Z bs4 = wr -> (1 <= wr <= 1000000)%Z ->
    getr regs 10 = Z_to_bv 64 dp ->
    exists regs', msteps SEGS (mkst regs (0x1fa14 : word) m rom) (mkst regs' (0x1faac : word) m rom)
      /\ getr regs' 9 = Z_to_bv 64 wr /\ getr regs' 12 = Z_to_bv 64 18446744073708551615
      /\ regs_agree (fun r => In r [9; 12; 13]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_C fx o10_reloc o10_code_ol rom). Qed.

Lemma pd_Cbad : forall regs m (dp wr : Z) bs4,
    (1 <= dp)%Z -> (dp + 28 <= 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (dp + 4)) 4 = Some bs4 -> bytes_le_to_Z bs4 = wr -> (0 <= wr < 2 ^ 32)%Z -> ~ (1 <= wr <= 1000000)%Z ->
    getr regs 10 = Z_to_bv 64 dp ->
    exists regs', msteps SEGS (mkst regs (0x1fa14 : word) m rom) (mkst regs' (0x1fa28 : word) m rom)
      /\ regs_agree (fun r => In r [9; 12; 13]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_Cbad fx o10_reloc o10_code_ol rom). Qed.

Lemma pd_D : forall regs m (dp hr : Z) bs8,
    (1 <= dp)%Z -> (dp + 28 <= 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (dp + 8)) 4 = Some bs8 -> bytes_le_to_Z bs8 = hr -> (1 <= hr <= 1000000)%Z ->
    getr regs 10 = Z_to_bv 64 dp -> getr regs 12 = Z_to_bv 64 18446744073708551615 ->
    exists regs', msteps SEGS (mkst regs (0x1faac : word) m rom) (mkst regs' (0x1fae0 : word) m rom)
      /\ getr regs' 18 = Z_to_bv 64 hr /\ regs_agree (fun r => In r [18; 13]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_D fx o10_reloc o10_code_ol rom). Qed.

Lemma pd_Dbad : forall regs m (dp hr : Z) bs8,
    (1 <= dp)%Z -> (dp + 28 <= 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (dp + 8)) 4 = Some bs8 -> bytes_le_to_Z bs8 = hr -> (0 <= hr < 2 ^ 32)%Z -> ~ (1 <= hr <= 1000000)%Z ->
    getr regs 10 = Z_to_bv 64 dp -> getr regs 12 = Z_to_bv 64 18446744073708551615 ->
    exists regs', msteps SEGS (mkst regs (0x1faac : word) m rom) (mkst regs' (0x1fab8 : word) m rom)
      /\ regs_agree (fun r => In r [18; 13]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_Dbad fx o10_reloc o10_code_ol rom). Qed.

Lemma pd_E : forall regs m (wr hr : Z),
    (1 <= wr <= 1000000)%Z -> (1 <= hr <= 1000000)%Z -> (wr * hr <= 400000000)%Z ->
    getr regs 9 = Z_to_bv 64 wr -> getr regs 18 = Z_to_bv 64 hr ->
    exists regs', msteps SEGS (mkst regs (0x1fae0 : word) m rom) (mkst regs' (0x1fb18 : word) m rom)
      /\ regs_agree (fun r => In r [12; 13]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_E fx o10_reloc o10_code_ol rom). Qed.

Lemma pd_Ebad : forall regs m (wr hr : Z),
    (1 <= wr <= 1000000)%Z -> (1 <= hr <= 1000000)%Z -> (400000000 < wr * hr)%Z ->
    getr regs 9 = Z_to_bv 64 wr -> getr regs 18 = Z_to_bv 64 hr ->
    exists regs', msteps SEGS (mkst regs (0x1fae0 : word) m rom) (mkst regs' (0x1faf0 : word) m rom)
      /\ regs_agree (fun r => In r [12; 13]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_Ebad fx o10_reloc o10_code_ol rom). Qed.

Lemma pd_F : forall regs m (dp nb ncr q dr wr hr : Z) bs20 bs12,
    (1 <= dp)%Z -> (dp + 28 <= 2 ^ 64)%Z -> (28 <= nb < 2 ^ 31)%Z -> q = (nb / 4)%Z ->
    rdn SEGS m (Z_to_bv 64 (dp + 20)) 4 = Some bs20 -> bytes_le_to_Z bs20 = ncr -> (0 <= ncr <= 256)%Z -> (ncr + 7 < q)%Z ->
    rdn SEGS m (Z_to_bv 64 (dp + 12)) 4 = Some bs12 -> bytes_le_to_Z bs12 = dr -> (0 <= dr < 2 ^ 32)%Z ->
    (0 <= wr < 2 ^ 64)%Z -> (0 <= hr < 2 ^ 64)%Z ->
    getr regs 10 = Z_to_bv 64 dp -> getr regs 11 = Z_to_bv 64 nb -> getr regs 9 = Z_to_bv 64 wr -> getr regs 18 = Z_to_bv 64 hr ->
    exists regs', msteps SEGS (mkst regs (0x1fb18 : word) m rom) (mkst regs' (0x15c78 : word) m rom)
      /\ getr regs' 23 = Z_to_bv 64 ncr /\ getr regs' 8 = Z_to_bv 64 nb /\ getr regs' 25 = Z_to_bv 64 dp
      /\ getr regs' 20 = Z_to_bv 64 (zx (sw32 dr))
      /\ getr regs' 10 = Z_to_bv 64 wr /\ getr regs' 11 = Z_to_bv 64 hr /\ getr regs' 12 = Z_to_bv 64 (zx (sw32 dr)) /\ getr regs' 1 = Z_to_bv 64 0x1fb4c
      /\ regs_agree (fun r => In r [1; 8; 10; 11; 12; 13; 20; 23; 25]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_F fx o10_reloc o10_code_ol o10_sites_ol rom). Qed.

Lemma pd_Fbad : forall regs m (dp nb ncr q : Z) bs20,
    (1 <= dp)%Z -> (dp + 28 <= 2 ^ 64)%Z -> (28 <= nb < 2 ^ 31)%Z -> q = (nb / 4)%Z ->
    rdn SEGS m (Z_to_bv 64 (dp + 20)) 4 = Some bs20 -> bytes_le_to_Z bs20 = ncr -> (0 <= ncr < 2 ^ 32)%Z -> ~ (ncr <= 256 /\ ncr + 7 < q)%Z ->
    getr regs 10 = Z_to_bv 64 dp -> getr regs 11 = Z_to_bv 64 nb ->
    exists regs', msteps SEGS (mkst regs (0x1fb18 : word) m rom) (mkst regs' (0x1fc00 : word) m rom)
      /\ regs_agree (fun r => In r [12; 13; 23]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_Fbad fx o10_reloc o10_code_ol rom). Qed.

Definition et_leaves : list (Z * Z) :=
    [(0x1fa50, 0x10e22); (0x1fa28, 0x1136a); (0x1fab8, 0x10470); (0x1faf0, 0x10382); (0x1fc00, 0x10f14); (0x1fc28, 0x10887)]%Z.
Lemma pd_ET : forall pc msg regs m,
    In (pc, msg) et_leaves ->
    rdn SEGS m (Z_to_bv 64 0x2ba18) 8 = Some (Z_to_le_bytes 8 0x2ca88) -> rdn SEGS m (Z_to_bv 64 0x2ca88) 4 = Some (Z_to_le_bytes 4 3) ->
    exists regs', msteps SEGS (mkst regs (Z_to_bv 64 pc) m rom) (mkst regs' (0x1fa74 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 msg /\ getr regs' 11 = Z_to_bv 64 0x10bc2
      /\ regs_agree (fun r => In r [10; 11]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_ET fx o10_reloc o10_code_ol o10_sites_ol rom). Qed.

Definition ej_leaves : list (Z * Z) := [(0x1fc88, 0x11028); (0x1fcc0, 0x1167c); (0x1fd28, 0x105c7)]%Z.
Lemma pd_EJ : forall pc msg regs m,
    In (pc, msg) ej_leaves ->
    rdn SEGS m (Z_to_bv 64 0x2ba18) 8 = Some (Z_to_le_bytes 8 0x2ca88) -> rdn SEGS m (Z_to_bv 64 0x2ca88) 4 = Some (Z_to_le_bytes 4 3) ->
    exists regs', msteps SEGS (mkst regs (Z_to_bv 64 pc) m rom) (mkst regs' (0x1573c : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 msg /\ getr regs' 11 = Z_to_bv 64 0x10bc2 /\ getr regs' 12 = Z_to_bv 64 0 /\ getr regs' 1 = Z_to_bv 64 0x1fd54
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_EJ fx o10_reloc o10_code_ol o10_sites_ol rom). Qed.

Definition pd_cells (m : word -> option byte) (s : Z) (ret : word) (sv : nat -> word) : Prop :=
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) /\
    rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (sv 8%nat)) /\
    rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (sv 9%nat)) /\
    rdn SEGS m (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 (sv 18%nat)) /\
    rdn SEGS m (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 (sv 19%nat)) /\
    rdn SEGS m (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 (sv 20%nat)) /\
    rdn SEGS m (Z_to_bv 64 (s - 56)) 8 = Some (word_to_le_bytes 8 (sv 21%nat)) /\
    rdn SEGS m (Z_to_bv 64 (s - 64)) 8 = Some (word_to_le_bytes 8 (sv 22%nat)) /\
    rdn SEGS m (Z_to_bv 64 (s - 72)) 8 = Some (word_to_le_bytes 8 (sv 23%nat)) /\
    rdn SEGS m (Z_to_bv 64 (s - 80)) 8 = Some (word_to_le_bytes 8 (sv 24%nat)) /\
    rdn SEGS m (Z_to_bv 64 (s - 88)) 8 = Some (word_to_le_bytes 8 (sv 25%nat)).
Lemma pd_X50 : forall regs m (s : Z) (ret : word) (sv : nat -> word),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> pd_cells m s ret sv -> getr regs 2 = Z_to_bv 64 (s - 112) ->
    exists regs', msteps SEGS (mkst regs (0x1fa74 : word) m rom) (mkst regs' (0x1573c : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 12 = Z_to_bv 64 0
      /\ getr regs' 8 = sv 8%nat /\ getr regs' 9 = sv 9%nat /\ getr regs' 18 = sv 18%nat /\ getr regs' 19 = sv 19%nat
      /\ getr regs' 20 = sv 20%nat /\ getr regs' 21 = sv 21%nat /\ getr regs' 22 = sv 22%nat /\ getr regs' 23 = sv 23%nat
      /\ getr regs' 24 = sv 24%nat /\ getr regs' 25 = sv 25%nat
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 12; 18; 19; 20; 21; 22; 23; 24; 25]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_X50 fx o10_reloc o10_code_ol o10_sites_ol rom). Qed.

Lemma pd_RET : forall regs m (s : Z) (ret : word) (sv : nat -> word),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret -> pd_cells m s ret sv -> getr regs 2 = Z_to_bv 64 (s - 112) ->
    exists regs', msteps SEGS (mkst regs (0x1fd5c : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret
      /\ getr regs' 8 = sv 8%nat /\ getr regs' 9 = sv 9%nat /\ getr regs' 18 = sv 18%nat /\ getr regs' 19 = sv 19%nat
      /\ getr regs' 20 = sv 20%nat /\ getr regs' 21 = sv 21%nat /\ getr regs' 22 = sv 22%nat /\ getr regs' 23 = sv 23%nat
      /\ getr regs' 24 = sv 24%nat /\ getr regs' 25 = sv 25%nat
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_RET fx o10_reloc o10_code_ol rom). Qed.

Lemma pd_R0 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x1fd58 : word) m rom) (mkst regs' (0x1fd5c : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 0 /\ regs_agree (fun r => In r [10]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_R0 fx o10_reloc o10_code_ol rom). Qed.

Lemma pd_J94 : forall regs m, exists regs', msteps SEGS (mkst regs (0x1f9b8 : word) m rom) (mkst regs' (0x1fd58 : word) m rom) /\ regs_agree (fun r => False) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_J94 fx o10_reloc o10_code_ol rom). Qed.

Lemma pd_J60 : forall regs m, exists regs', msteps SEGS (mkst regs (0x1fc84 : word) m rom) (mkst regs' (0x1fd58 : word) m rom) /\ regs_agree (fun r => False) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_J60 fx o10_reloc o10_code_ol rom). Qed.

Lemma pd_J30 : forall regs m, exists regs', msteps SEGS (mkst regs (0x1fd54 : word) m rom) (mkst regs' (0x1fd5c : word) m rom) /\ regs_agree (fun r => False) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_J30 fx o10_reloc o10_code_ol rom). Qed.

Lemma pd_G0 : forall regs m (s : Z),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 112)) 112 = true ->
    getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs', msteps SEGS (mkst regs (0x1fb4c : word) m rom)
                              (mkst regs' (0x1fc28 : word) (wbytes m (Z_to_bv 64 (s - 104)) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ regs_agree (fun r => False) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_G0 fx o10_reloc o10_code_ol rom). Qed.

Lemma pd_G : forall regs m (s dp nb nc pix1 wpl hr ir : Z) (v1 : pixv) bsi,
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 112)) 112 = true ->
    PIXat m pix1 v1 -> (4096 <= pix1)%Z -> (pix1 + 64 <= s - 112)%Z -> p_wpl v1 = wpl -> (1 <= hr <= 1000000)%Z -> (0 <= wpl)%Z -> (4 * (wpl * hr) <= 67108864)%Z ->
    (0 <= nc <= 256)%Z -> (28 <= nb < 2 ^ 31)%Z -> (4 * nc + 32 <= nb)%Z -> (1 <= dp)%Z -> (dp + nb <= s - 112)%Z ->
    rdn SEGS m (Z_to_bv 64 (dp + 4 * nc + 24)) 4 = Some bsi -> bytes_le_to_Z bsi = ir -> (0 <= ir < 2 ^ 32)%Z ->
    getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 10 = Z_to_bv 64 pix1 -> getr regs 23 = Z_to_bv 64 nc -> getr regs 8 = Z_to_bv 64 nb ->
    getr regs 25 = Z_to_bv 64 dp -> getr regs 18 = Z_to_bv 64 hr ->
    exists regs', msteps SEGS (mkst regs (0x1fb4c : word) m rom)
                              (mkst regs' (0x15fb4 : word) (wbytes m (Z_to_bv 64 (s - 104)) (word_to_le_bytes 8 (Z_to_bv 64 pix1))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 112) /\ getr regs' 10 = Z_to_bv 64 (s - 104) /\ getr regs' 1 = Z_to_bv 64 0x1fb84
      /\ getr regs' 19 = Z_to_bv 64 nc /\ getr regs' 24 = Z_to_bv 64 (dp + 4 * nc) /\ getr regs' 21 = Z_to_bv 64 (zx (sw32 ir))
      /\ getr regs' 8 = Z_to_bv 64 (4 * (wpl * hr)) /\ getr regs' 22 = Z_to_bv 64 (nb - 4 * nc - 28)
      /\ regs_agree (fun r => In r [1; 8; 10; 11; 19; 21; 22; 24]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_G fx o10_reloc o10_code_ol o10_sites_ol rom). Qed.

Lemma pd_H : forall regs m (sz wr hr d : Z),
    (0 <= sz < 2 ^ 32)%Z ->
    getr regs 8 = Z_to_bv 64 sz -> getr regs 22 = Z_to_bv 64 sz -> getr regs 21 = Z_to_bv 64 sz ->
    getr regs 9 = Z_to_bv 64 wr -> getr regs 18 = Z_to_bv 64 hr -> getr regs 20 = Z_to_bv 64 d ->
    exists regs', msteps SEGS (mkst regs (0x1fb84 : word) m rom) (mkst regs' (0x15ab0 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 wr /\ getr regs' 11 = Z_to_bv 64 hr /\ getr regs' 12 = Z_to_bv 64 d /\ getr regs' 1 = Z_to_bv 64 0x1fb9c
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_H fx o10_reloc o10_code_ol o10_sites_ol rom). Qed.

Lemma pd_Hbad : forall regs m (sz msz isz : Z),
    (0 <= sz < 2 ^ 32)%Z -> (0 <= msz < 2 ^ 32)%Z -> (0 <= isz < 2 ^ 64)%Z -> (sz <> msz \/ sz <> isz) ->
    rdn SEGS m (Z_to_bv 64 0x2ba18) 8 = Some (Z_to_le_bytes 8 0x2ca88) -> rdn SEGS m (Z_to_bv 64 0x2ca88) 4 = Some (Z_to_le_bytes 4 3) ->
    getr regs 8 = Z_to_bv 64 sz -> getr regs 22 = Z_to_bv 64 msz -> getr regs 21 = Z_to_bv 64 isz ->
    exists regs', msteps SEGS (mkst regs (0x1fb84 : word) m rom) (mkst regs' (0x156a0 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 0x10a28 /\ getr regs' 11 = Z_to_bv 64 0x10bc2 /\ getr regs' 1 = Z_to_bv 64 0x1fc84
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_Hbad fx o10_reloc o10_code_ol o10_sites_ol rom). Qed.

Lemma pd_I0 : forall regs m (s : Z),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 112)) 112 = true ->
    getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs', msteps SEGS (mkst regs (0x1fb9c : word) m rom)
                              (mkst regs' (0x1fc88 : word) (wbytes m (Z_to_bv 64 (s - 112)) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ regs_agree (fun r => False) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_I0 fx o10_reloc o10_code_ol rom). Qed.

Lemma pd_I1 : forall regs m (s pixd : Z),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 112)) 112 = true -> (1 <= pixd < 2 ^ 64)%Z ->
    getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 10 = Z_to_bv 64 pixd -> getr regs 23 = Z_to_bv 64 0 ->
    exists regs', msteps SEGS (mkst regs (0x1fb9c : word) m rom)
                              (mkst regs' (0x1fcec : word) (wbytes m (Z_to_bv 64 (s - 112)) (word_to_le_bytes 8 (Z_to_bv 64 pixd))) rom)
      /\ getr regs' 9 = Z_to_bv 64 0 /\ getr regs' 10 = Z_to_bv 64 pixd /\ regs_agree (fun r => In r [9]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_I1 fx o10_reloc o10_code_ol rom). Qed.

Lemma pd_I2 : forall regs m (s pixd dp nc : Z),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 112)) 112 = true -> (1 <= pixd < 2 ^ 64)%Z -> (1 <= nc <= 256)%Z -> (0 <= dp < 2 ^ 64)%Z ->
    getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 10 = Z_to_bv 64 pixd -> getr regs 23 = Z_to_bv 64 nc -> getr regs 25 = Z_to_bv 64 dp -> getr regs 19 = Z_to_bv 64 nc ->
    exists regs', msteps SEGS (mkst regs (0x1fb9c : word) m rom)
                              (mkst regs' (0x19660 : word) (wbytes m (Z_to_bv 64 (s - 112)) (word_to_le_bytes 8 (Z_to_bv 64 pixd))) rom)
      /\ getr regs' 10 = Z_to_bv 64 (dp + 24) /\ getr regs' 11 = Z_to_bv 64 4 /\ getr regs' 12 = Z_to_bv 64 nc /\ getr regs' 1 = Z_to_bv 64 0x1fbb8
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_I2 fx o10_reloc o10_code_ol o10_sites_ol rom). Qed.

Lemma pd_J0 : forall regs m (s : Z),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs', msteps SEGS (mkst regs (0x1fbb8 : word) m rom) (mkst regs' (0x15fb4 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 (s - 112) /\ getr regs' 1 = Z_to_bv 64 0x1fcc0 /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_J0 fx o10_reloc o10_code_ol o10_sites_ol rom). Qed.

Lemma pd_J1 : forall regs m (s cm pixd : Z),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= cm < 2 ^ 64)%Z -> (0 <= pixd < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 112)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 pixd)) ->
    getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 10 = Z_to_bv 64 cm ->
    exists regs', msteps SEGS (mkst regs (0x1fbb8 : word) m rom) (mkst regs' (0x166bc : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 cm /\ getr regs' 9 = Z_to_bv 64 cm /\ getr regs' 1 = Z_to_bv 64 0x1fbcc
      /\ regs_agree (fun r => In r [1; 9; 10; 11]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_J1 fx o10_reloc o10_code_ol o10_sites_ol rom). Qed.

Lemma pd_K : forall regs m (s pixd : Z),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= pixd < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 112)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 pixd)) ->
    getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs', msteps SEGS (mkst regs (0x1fbcc : word) m rom) (mkst regs' (0x1fcec : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 pixd /\ regs_agree (fun r => In r [10]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_K fx o10_reloc o10_code_ol rom). Qed.

Lemma pd_GD : forall regs m (pixd e8 sz : Z) (v : pixv),
    PIXat m pixd v -> (4096 <= pixd)%Z -> (0 <= e8)%Z -> (e8 + 28 < 2 ^ 64)%Z ->
    getr regs 10 = Z_to_bv 64 pixd -> getr regs 24 = Z_to_bv 64 e8 -> getr regs 8 = Z_to_bv 64 sz ->
    exists regs', msteps SEGS (mkst regs (0x1fcec : word) m rom) (mkst regs' (0x29fc8 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 (p_data v) /\ getr regs' 11 = Z_to_bv 64 (e8 + 28) /\ getr regs' 12 = Z_to_bv 64 sz /\ getr regs' 1 = Z_to_bv 64 0x1fcfc
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_GD fx o10_reloc o10_code_ol o10_sites_ol rom). Qed.

Lemma pd_L0 : forall regs m (s pixd : Z),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= pixd < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 112)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 pixd)) ->
    getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 23 = Z_to_bv 64 0 ->
    exists regs', msteps SEGS (mkst regs (0x1fcfc : word) m rom) (mkst regs' (0x1fd5c : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 pixd /\ regs_agree (fun r => In r [10]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_L0 fx o10_reloc o10_code_ol rom). Qed.

Lemma pd_L1 : forall regs m (s pixd nc cm : Z),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= pixd < 2 ^ 64)%Z -> (1 <= nc <= 256)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 112)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 pixd)) ->
    getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 23 = Z_to_bv 64 nc -> getr regs 9 = Z_to_bv 64 cm ->
    exists regs', msteps SEGS (mkst regs (0x1fcfc : word) m rom) (mkst regs' (0x18a08 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 cm /\ getr regs' 11 = Z_to_bv 64 pixd /\ getr regs' 12 = Z_to_bv 64 (s - 92) /\ getr regs' 1 = Z_to_bv 64 0x1fd10
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_L1 fx o10_reloc o10_code_ol o10_sites_ol rom). Qed.

Lemma pd_M1 : forall regs m (s pixd : Z),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= pixd < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 92)) 4 = Some (Z_to_le_bytes 4 1) ->
    rdn SEGS m (Z_to_bv 64 (s - 112)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 pixd)) ->
    getr regs 2 = Z_to_bv 64 (s - 112) ->
    exists regs', msteps SEGS (mkst regs (0x1fd10 : word) m rom) (mkst regs' (0x1fd5c : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 pixd /\ regs_agree (fun r => In r [10]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_M1 fx o10_reloc o10_code_ol rom). Qed.

Lemma pd_M0 : forall regs m (s : Z),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 92)) 4 = Some (Z_to_le_bytes 4 0) ->
    getr regs 2 = Z_to_bv 64 (s - 112) ->
    exists regs', msteps SEGS (mkst regs (0x1fd10 : word) m rom) (mkst regs' (0x15fb4 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 (s - 112) /\ getr regs' 1 = Z_to_bv 64 0x1fd28 /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_M0 fx o10_reloc o10_code_ol o10_sites_ol rom). Qed.

End Segs.

End DeserA.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).      (* [comment removed for export] *)
End O10LeptDeserA.

From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.OL Require LeptPixHdr.
Module O10LeptPixHdr.
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
Import OSSVerify.leptonica.fhmtgen_fuzzer.images.Plain.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StepTac.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AllocIface.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PureModel.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.VmLedger.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StoreOk.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.MemSplit.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefMemcpyLib.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StartupTac.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.WalkTac.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocBase.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocSure.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.SumWalkTac.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.SumSpecs.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.WalksLib.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.W2Lib.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.LibAtomic.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.LeptDefs.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.LeptStructs.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.LeptArith.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.O10.O10LeptStderr.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.O10.O10LeptBase.
Import O10CL7a.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.LeptRoom.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.Reloc.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.RelocLept.
Import O10Kit.
(* [comment removed for export] *)










Import O10CL7a.O10LeptErr.





Import O10Kit.O10Reloc. Import O10Kit.O10RelocCode. Import O10Kit.O10RelocSites. Import O10Kit.O10RelocImg. Import O10Kit.O10RelocOL.
Import O10Kit.O10RelocMusl. Import O10Kit.O10LeptEnv.
Import O10CL7a.O10LeptG.
Import ListNotations.
Open Scope bv_scope.

Section PixHdr.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LL16} {P16 : O10Pins}.
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
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x3d100 ->
  getr regs 10 = Z_to_bv 64 w -> getr regs 11 = Z_to_bv 64 h -> getr regs 12 = Z_to_bv 64 d ->
  (1 <= w <= 1000000)%Z -> (1 <= h <= 1000000)%Z -> (w * h <= 400000000)%Z -> (0 <= d < 2 ^ 64)%Z ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     ((getr regs' 10 = Z_to_bv 64 0 /\ forall q, live A' q = live A q)
      \/ (exists pix, getr regs' 10 = Z_to_bv 64 pix /\ (hdr_ok w h d /\ pix_new C A A' m' pix (pix_hdr w h d)))) ->
     roomtr A (m_vmmaps md) A' vm' RK_hdr RB_hdr ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x15c78 : word) m al_rom) md) S.
Proof. rl_tail (@LeptPixHdr.pixCreateHeader_W fx o10_reloc o10_code o10_sites o10_code_ol o10_sites_ol o10_lept o10_img_ol o10_data o10_img o10_rw o10_pf o10_lenv_ol AL CL ASR PINS (o10_pinsG P16)). Qed.

End PixHdr.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).      (* [comment removed for export] *)
End O10LeptPixHdr.

From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require LeptRecs.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require LeptSel.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.O10 Require O10_code_fhFG.
Module O10LeptSelSegs.
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
Import OSSVerify.leptonica.fhmtgen_fuzzer.images.Plain.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StepTac.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AllocIface.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PureModel.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.VmLedger.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StoreOk.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.MemSplit.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefMemcpyLib.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StartupTac.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.WalkTac.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocBase.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocSure.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.SumWalkTac.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.SumSpecs.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.WalksLib.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.W2Lib.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.LibAtomic.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.LeptDefs.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.LeptStructs.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.LeptArith.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.LeptArith2.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.LeptRecs.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.LeptSel.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.O10.O10LeptStderr.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.O10.O10LeptBase.
Import O10CL7a.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.O10.O10_code_fhFG.
(* [comment removed for export] *)









Import O10CL7a.O10LeptSel_iface.

Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].

(* [comment removed for export] *)
Ltac condZm :=
  pin; rewrite ?c_eq_Zm; first [apply Z.eqb_neq | apply Z.eqb_eq];
  repeat match goal with |- context [(?a mod 2 ^ 64)%Z] => rewrite (Z.mod_small a (2 ^ 64)) by lia end; lia.

(* [comment removed for export] *)
Lemma bytes_at_hd : forall m (l : Z) (a : byte) t, bytes_at m l (a :: t) -> (0 <= l)%Z -> (l + 1 <= 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 l) 1 = Some [a].
Proof.
  intros m l a t HB Hl Hl1. apply (bytes_at_rdn SEGS m l [a]); [lia | cbn; lia |].
  intros i Hi. cbn [length] in Hi. assert (i = 0%Z) by lia. subst i. apply (HB 0%Z). cbn [length]. lia.
Qed.
Lemma bytes_at_tl : forall m (l : Z) (a : byte) t, bytes_at m l (a :: t) -> bytes_at m (l + 1) t.
Proof.
  intros m l a t HB i Hi. replace (l + 1 + i)%Z with (l + (i + 1))%Z by lia. rewrite (HB (i + 1)%Z) by (cbn [length]; lia).
  f_equal. replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia. reflexivity.
Qed.

Section SelSegs.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LL16} {P16 : O10Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma selaGetCount_run_W : selaGetCount_run.
Proof.
  intros rom regs m sela n na arr ret R Hs Hal Hn H1 Hret H10.
  pose proof (RECat_range m sela _ R) as [_ RG]. cbn in RG.
  pose proof (REC_rd' SEGS m sela (sela_flds n na arr) 0 4 (Z_to_bv 64 sela) n R ltac:(cbn; lia) eq_refl
                ltac:(cbn [fld_off sela_flds Z.of_nat]; f_equal; lia) eq_refl) as Rn.
  unfold PC_selaGetCount. replace (Z_to_bv 64 0x207e8) with (0x207e8 : word) by (apply bv_eq; reflexivity).
  eexists. split.
  - stepb_ft F_206ec D_206ec ltac:(condZ).
    stepLD F_206f0 D_206f0 (Z_to_le_bytes 4 n) (Z_to_bv 64 n) ltac:(addr_norm; exact Rn) ltac:(apply lez4; lia).
    rewrite (v_lw_small n) by lia.
    stepret F_206f4 D_206f4 ret ltac:(exact H1).
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

Lemma selaGetSel_run_W : selaGetSel_run.
Proof.
  intros rom regs m sela n na arr i seli ret R Hs Hal Hi Hn Ha Ha64 Haal Bc Hseli H1 Hret H10 H11.
  pose proof (RECat_range m sela _ R) as [_ RG]. cbn in RG.
  pose proof R as (_ & _ & WF & _). cbn in WF.
  pose proof (REC_rd' SEGS m sela (sela_flds n na arr) 0 4 (Z_to_bv 64 sela) n R ltac:(cbn; lia) eq_refl
                ltac:(cbn [fld_off sela_flds Z.of_nat]; f_equal; lia) eq_refl) as Rn.
  pose proof (REC_rd' SEGS m sela (sela_flds n na arr) 2 8 (Z_to_bv 64 (sela + 8)) arr R ltac:(cbn; lia) eq_refl eq_refl eq_refl) as Rarr.
  pose proof (bytes_at_rdn SEGS m (arr + 8 * i) (Z_to_le_bytes 8 seli) ltac:(lia) ltac:(rewrite length_Z_to_le_bytes; lia) Bc) as Rc.
  rewrite length_Z_to_le_bytes in Rc.
  unfold PC_selaGetSel. replace (Z_to_bv 64 0x20828) with (0x20828 : word) by (apply bv_eq; reflexivity).
  eexists. split.
  - stepb_ft F_2072c D_2072c ltac:(condZ).
    stepb_ft F_20730 D_20730 ltac:(condZ).
    stepLD F_20734 D_20734 (Z_to_le_bytes 4 n) (Z_to_bv 64 n) ltac:(addr_norm; exact Rn) ltac:(apply lez4; lia).
    rewrite (v_lw_small n) by lia.
    stepb_ft F_20738 D_20738 ltac:(condZ).
    stepLD F_2073c D_2073c (Z_to_le_bytes 8 arr) (Z_to_bv 64 arr) ltac:(addr_norm; exact Rarr) ltac:(apply lez8; lia).
    stepiv F_20740 D_20740 (Z_to_bv 64 (8 * i)) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; lia).
    zv F_20744 D_20744 (Z_to_bv 64 (arr + 8 * i)).
    stepLD F_20748 D_20748 (Z_to_le_bytes 8 seli) (Z_to_bv 64 seli) ltac:(addr_norm; exact Rc) ltac:(apply lez8; lia).
    stepret F_2074c D_2074c ret ltac:(exact H1).
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

Lemma selGetName_run_W : selGetName_run.
Proof.
  intros rom regs m sel sy sx cy cx data name ret R Hs Hal H1 Hret H10.
  pose proof (RECat_range m sel _ R) as [_ RG]. cbn in RG.
  pose proof R as (_ & _ & WF & _). cbn in WF.
  pose proof (REC_rd' SEGS m sel (sel_flds sy sx cy cx data name) 5 8 (Z_to_bv 64 (sel + 24)) name R ltac:(cbn; lia) eq_refl eq_refl eq_refl) as Rnm.
  unfold PC_selGetName. replace (Z_to_bv 64 0x208ac) with (0x208ac : word) by (apply bv_eq; reflexivity).
  eexists. split.
  - stepb_ft F_207b0 D_207b0 ltac:(condZ).
    stepLD F_207b4 D_207b4 (Z_to_le_bytes 8 name) (Z_to_bv 64 name) ltac:(addr_norm; exact Rnm) ltac:(apply lez8; lia).
    stepret F_207b8 D_207b8 ret ltac:(exact H1).
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma cstr_inv : forall (a : byte) t, cstr (a :: t) -> (a = Z_to_bv 8 0 /\ t = []) \/ (a <> Z_to_bv 8 0 /\ cstr t).
Proof.
  intros a t (s & E & NZ). destruct s as [|b s']; cbn [app] in E; injection E as -> ->.
  - left. split; reflexivity.
  - right. inversion NZ as [|? ? Hb Hs']; subst. split; [exact Hb|]. exists s'. split; [reflexivity | exact Hs'].
Qed.
Lemma cstr_nonnil : forall l, cstr l -> exists a t, l = a :: t.
Proof. intros l (s & -> & _). destruct s as [|b s']; cbn [app]; eauto. Qed.
Lemma byte_u0 : forall a : byte, u a = 0%Z -> a = Z_to_bv 8 0.
Proof. intros a H. apply bv_eq. rewrite H. reflexivity. Qed.
Lemma byte_ueq : forall a b : byte, u a = u b -> a = b.
Proof. intros a b H. apply bv_eq. exact H. Qed.

Section StrcmpSegs.
Variable rom : word -> option byte.

  (* [comment removed for export] *)
  Lemma sc_E : forall regs m (x y : Z) (ret : word),
    getr regs 1 = ret -> ret_ok ret -> getr regs 12 = Z_to_bv 64 x -> getr regs 13 = Z_to_bv 64 y ->
    exists regs',
      msteps SEGS (mkst regs (0x2a4f4 : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 10 = Z_to_bv 64 (x - y) /\ regs_agree (fun r => In r [10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m x y ret H1 Hret H12 H13. eexists. split.
    - zv F_29fb8 D_29fb8 (Z_to_bv 64 (x - y)).
      stepret F_29fbc D_29fbc ret ltac:(exact H1).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma sc_L_exit : forall regs m (l r : Z) (a b : byte),
    (1 <= l)%Z -> (l + 1 < 2 ^ 64)%Z -> (1 <= r)%Z -> (r + 1 < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 l) 1 = Some [a] -> rdn SEGS m (Z_to_bv 64 r) 1 = Some [b] ->
    (u a = 0 \/ u a <> u b)%Z ->
    getr regs 10 = Z_to_bv 64 l -> getr regs 11 = Z_to_bv 64 r ->
    exists regs',
      msteps SEGS (mkst regs (0x2a4dc : word) m rom) (mkst regs' (0x2a4f4 : word) m rom)
      /\ getr regs' 12 = Z_to_bv 64 (u a) /\ getr regs' 13 = Z_to_bv 64 (u b) /\ getr regs' 1 = getr regs 1
      /\ regs_agree (fun r => In r [10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m l r a b Hl Hl1 Hr Hr1 Ra Rb Hex H10 H11.
    pose proof (u8_range a) as Ua. pose proof (u8_range b) as Ub.
    destruct (Z.eq_dec (u a) 0) as [E0|N0].
    - eexists. split.
      + stepLBU F_29fa0 D_29fa0 a ltac:(addr_norm; exact Ra).
        stepLBU F_29fa4 D_29fa4 b ltac:(addr_norm; exact Rb).
        stepb_tk F_29fa8 D_29fa8 ltac:(condZ).
        apply mst_refl.
      + repeat split; gres; pin; try reflexivity. solve_regs_agree.
    - eexists. split.
      + stepLBU F_29fa0 D_29fa0 a ltac:(addr_norm; exact Ra).
        stepLBU F_29fa4 D_29fa4 b ltac:(addr_norm; exact Rb).
        stepb_ft F_29fa8 D_29fa8 ltac:(condZ).
        zv F_29fac D_29fac (Z_to_bv 64 (r + 1)).
        zv F_29fb0 D_29fb0 (Z_to_bv 64 (l + 1)).
        stepb_ft F_29fb4 D_29fb4 ltac:(condZ).
        apply mst_refl.
      + repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma sc_L_cont : forall regs m (l r : Z) (a b : byte),
    (1 <= l)%Z -> (l + 1 < 2 ^ 64)%Z -> (1 <= r)%Z -> (r + 1 < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 l) 1 = Some [a] -> rdn SEGS m (Z_to_bv 64 r) 1 = Some [b] ->
    (u a <> 0)%Z -> (u a = u b)%Z ->
    getr regs 10 = Z_to_bv 64 l -> getr regs 11 = Z_to_bv 64 r ->
    exists regs',
      msteps SEGS (mkst regs (0x2a4dc : word) m rom) (mkst regs' (0x2a4dc : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 (l + 1) /\ getr regs' 11 = Z_to_bv 64 (r + 1) /\ getr regs' 1 = getr regs 1
      /\ regs_agree (fun r => In r [10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m l r a b Hl Hl1 Hr Hr1 Ra Rb N0 Eab H10 H11.
    pose proof (u8_range a) as Ua. pose proof (u8_range b) as Ub.
    eexists. split.
    - stepLBU F_29fa0 D_29fa0 a ltac:(addr_norm; exact Ra).
      stepLBU F_29fa4 D_29fa4 b ltac:(addr_norm; exact Rb).
      stepb_ft F_29fa8 D_29fa8 ltac:(condZ).
      zv F_29fac D_29fac (Z_to_bv 64 (r + 1)).
      zv F_29fb0 D_29fb0 (Z_to_bv 64 (l + 1)).
      stepb_tk F_29fb4 D_29fb4 ltac:(condZ).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma sc_0_exit : forall regs m (l r : Z) (a b : byte),
    (1 <= l)%Z -> (l + 1 < 2 ^ 64)%Z -> (1 <= r)%Z -> (r + 1 < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 l) 1 = Some [a] -> rdn SEGS m (Z_to_bv 64 r) 1 = Some [b] ->
    (u a = 0 \/ u a <> u b)%Z ->
    getr regs 10 = Z_to_bv 64 l -> getr regs 11 = Z_to_bv 64 r ->
    exists regs',
      msteps SEGS (mkst regs (0x2a4c4 : word) m rom) (mkst regs' (0x2a4f4 : word) m rom)
      /\ getr regs' 12 = Z_to_bv 64 (u a) /\ getr regs' 13 = Z_to_bv 64 (u b) /\ getr regs' 1 = getr regs 1
      /\ regs_agree (fun r => In r [10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m l r a b Hl Hl1 Hr Hr1 Ra Rb Hex H10 H11.
    pose proof (u8_range a) as Ua. pose proof (u8_range b) as Ub.
    destruct (Z.eq_dec (u a) 0) as [E0|N0].
    - eexists. split.
      + stepLBU F_29f88 D_29f88 a ltac:(addr_norm; exact Ra).
        stepLBU F_29f8c D_29f8c b ltac:(addr_norm; exact Rb).
        stepb_tk F_29f90 D_29f90 ltac:(condZ).
        apply mst_refl.
      + repeat split; gres; pin; try reflexivity. solve_regs_agree.
    - eexists. split.
      + stepLBU F_29f88 D_29f88 a ltac:(addr_norm; exact Ra).
        stepLBU F_29f8c D_29f8c b ltac:(addr_norm; exact Rb).
        stepb_ft F_29f90 D_29f90 ltac:(condZ).
        stepb_tk F_29f94 D_29f94 ltac:(condZ).
        apply mst_refl.
      + repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma sc_0_cont : forall regs m (l r : Z) (a b : byte),
    (1 <= l)%Z -> (l + 1 < 2 ^ 64)%Z -> (1 <= r)%Z -> (r + 1 < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 l) 1 = Some [a] -> rdn SEGS m (Z_to_bv 64 r) 1 = Some [b] ->
    (u a <> 0)%Z -> (u a = u b)%Z ->
    getr regs 10 = Z_to_bv 64 l -> getr regs 11 = Z_to_bv 64 r ->
    exists regs',
      msteps SEGS (mkst regs (0x2a4c4 : word) m rom) (mkst regs' (0x2a4dc : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 (l + 1) /\ getr regs' 11 = Z_to_bv 64 (r + 1) /\ getr regs' 1 = getr regs 1
      /\ regs_agree (fun r => In r [10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m l r a b Hl Hl1 Hr Hr1 Ra Rb N0 Eab H10 H11.
    pose proof (u8_range a) as Ua. pose proof (u8_range b) as Ub.
    eexists. split.
    - stepLBU F_29f88 D_29f88 a ltac:(addr_norm; exact Ra).
      stepLBU F_29f8c D_29f8c b ltac:(addr_norm; exact Rb).
      stepb_ft F_29f90 D_29f90 ltac:(condZ).
      stepb_ft F_29f94 D_29f94 ltac:(condZ).
      zv F_29f98 D_29f98 (Z_to_bv 64 (r + 1)).
      zv F_29f9c D_29f9c (Z_to_bv 64 (l + 1)).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma sc_loop : forall (la lb : list byte) regs m (l r : Z) (ret : word),
    rd_str SEGS m l la -> rd_str SEGS m r lb -> cstr la -> cstr lb ->
    (1 <= l)%Z -> (l + Z.of_nat (length la) < 2 ^ 64)%Z -> (1 <= r)%Z -> (r + Z.of_nat (length lb) < 2 ^ 64)%Z ->
    getr regs 1 = ret -> ret_ok ret -> getr regs 10 = Z_to_bv 64 l -> getr regs 11 = Z_to_bv 64 r ->
    exists regs',
      msteps SEGS (mkst regs (0x2a4dc : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 10 = Z_to_bv 64 (strcmp_Z la lb) /\ regs_agree (fun x => In x [10; 11; 12; 13]%list) regs regs'.
  Proof.
    induction la as [|a ta IH]; intros lb regs m l r ret Ba Bb Ca Cb Hl Hla Hr Hlb H1 Hret H10 H11.
    { destruct (cstr_nonnil _ Ca) as (? & ? & X). discriminate X. }
    destruct (cstr_nonnil _ Cb) as (b & tb & ->). cbn [length] in Hla, Hlb.
    pose proof (rd_str_hd SEGS m l a ta Ba) as Ra.
    pose proof (rd_str_hd SEGS m r b tb Bb) as Rb.
    cbn [strcmp_Z]. destruct (Z.eqb_spec (u a) 0) as [E0|N0]; [| destruct (Z.eqb_spec (u a) (u b)) as [Eab|Nab]].
    - destruct (sc_L_exit regs m l r a b Hl ltac:(lia) Hr ltac:(lia) Ra Rb (or_introl E0) H10 H11) as (r1 & RUN1 & Q12 & Q13 & Q1 & AG1).
      destruct (sc_E r1 m (u a) (u b) ret ltac:(rewrite Q1; exact H1) Hret Q12 Q13) as (r2 & RUN2 & P10 & AG2).
      exists r2. split; [exact (msteps_trans SEGS _ _ _ RUN1 RUN2)|]. split; [exact P10 | exact (regs_agree_trans _ _ _ _ AG1 AG2)].
    - destruct (cstr_inv a ta Ca) as [[X _]|[_ Cta]]; [exfalso; apply N0; rewrite X; reflexivity|].
      destruct (cstr_inv b tb Cb) as [[X _]|[_ Ctb]]; [exfalso; apply N0; rewrite Eab, X; reflexivity|].
      destruct (sc_L_cont regs m l r a b Hl ltac:(lia) Hr ltac:(lia) Ra Rb N0 Eab H10 H11) as (r1 & RUN1 & Q10 & Q11 & Q1 & AG1).
      destruct (IH tb r1 m (l + 1)%Z (r + 1)%Z ret (rd_str_tl SEGS m l a ta Ba) (rd_str_tl SEGS m r b tb Bb) Cta Ctb ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(rewrite Q1; exact H1) Hret Q10 Q11) as (r2 & RUN2 & P10 & AG2).
      exists r2. split; [exact (msteps_trans SEGS _ _ _ RUN1 RUN2)|]. split; [exact P10 | exact (regs_agree_trans _ _ _ _ AG1 AG2)].
    - destruct (sc_L_exit regs m l r a b Hl ltac:(lia) Hr ltac:(lia) Ra Rb (or_intror Nab) H10 H11) as (r1 & RUN1 & Q12 & Q13 & Q1 & AG1).
      destruct (sc_E r1 m (u a) (u b) ret ltac:(rewrite Q1; exact H1) Hret Q12 Q13) as (r2 & RUN2 & P10 & AG2).
      exists r2. split; [exact (msteps_trans SEGS _ _ _ RUN1 RUN2)|]. split; [exact P10 | exact (regs_agree_trans _ _ _ _ AG1 AG2)].
  Qed.
End StrcmpSegs.

Lemma strcmp_run_W : strcmp_run.
Proof.
  intros rom regs m l r la lb ret Ba Bb Ca Cb Hl Hla Hr Hlb H1 Hret H10 H11.
  destruct (cstr_nonnil _ Ca) as (a & ta & ->). destruct (cstr_nonnil _ Cb) as (b & tb & ->). cbn [length] in Hla, Hlb.
  pose proof (rd_str_hd SEGS m l a ta Ba) as Ra.
  pose proof (rd_str_hd SEGS m r b tb Bb) as Rb.
  unfold PC_strcmp. replace (Z_to_bv 64 0x2a4c4) with (0x2a4c4 : word) by (apply bv_eq; reflexivity).
  cbn [strcmp_Z]. destruct (Z.eqb_spec (u a) 0) as [E0|N0]; [| destruct (Z.eqb_spec (u a) (u b)) as [Eab|Nab]].
  - destruct (sc_0_exit rom regs m l r a b Hl ltac:(lia) Hr ltac:(lia) Ra Rb (or_introl E0) H10 H11) as (r1 & RUN1 & Q12 & Q13 & Q1 & AG1).
    destruct (sc_E rom r1 m (u a) (u b) ret ltac:(rewrite Q1; exact H1) Hret Q12 Q13) as (r2 & RUN2 & P10 & AG2).
    exists r2. split; [exact (msteps_trans SEGS _ _ _ RUN1 RUN2)|]. split; [exact P10 | exact (regs_agree_trans _ _ _ _ AG1 AG2)].
  - destruct (cstr_inv a ta Ca) as [[X _]|[_ Cta]]; [exfalso; apply N0; rewrite X; reflexivity|].
    destruct (cstr_inv b tb Cb) as [[X _]|[_ Ctb]]; [exfalso; apply N0; rewrite Eab, X; reflexivity|].
    destruct (sc_0_cont rom regs m l r a b Hl ltac:(lia) Hr ltac:(lia) Ra Rb N0 Eab H10 H11) as (r1 & RUN1 & Q10 & Q11 & Q1 & AG1).
    destruct (sc_loop rom ta tb r1 m (l + 1)%Z (r + 1)%Z ret (rd_str_tl SEGS m l a ta Ba) (rd_str_tl SEGS m r b tb Bb) Cta Ctb ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(rewrite Q1; exact H1) Hret Q10 Q11) as (r2 & RUN2 & P10 & AG2).
    exists r2. split; [exact (msteps_trans SEGS _ _ _ RUN1 RUN2)|]. split; [exact P10 | exact (regs_agree_trans _ _ _ _ AG1 AG2)].
  - destruct (sc_0_exit rom regs m l r a b Hl ltac:(lia) Hr ltac:(lia) Ra Rb (or_intror Nab) H10 H11) as (r1 & RUN1 & Q12 & Q13 & Q1 & AG1).
    destruct (sc_E rom r1 m (u a) (u b) ret ltac:(rewrite Q1; exact H1) Hret Q12 Q13) as (r2 & RUN2 & P10 & AG2).
    exists r2. split; [exact (msteps_trans SEGS _ _ _ RUN1 RUN2)|]. split; [exact P10 | exact (regs_agree_trans _ _ _ _ AG1 AG2)].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition SL_C1 : Z := 0x0101010101010100.
Definition SL_C2 : Z := 0x8080808080808080.
(* [comment removed for export] *)
Definition strlen_stop (wv : word) : Prop :=
  c_eq (v_and (v_or (v_sub (Z_to_bv 64 SL_C1) wv) wv) (Z_to_bv 64 SL_C2)) (Z_to_bv 64 SL_C2) = false.

Lemma bytes_at_nth1 : forall m (l : Z) bs (i : Z), bytes_at m l bs -> (0 <= l)%Z -> (l + Z.of_nat (length bs) <= 2 ^ 64)%Z ->
  (0 <= i < Z.of_nat (length bs))%Z -> rdn SEGS m (Z_to_bv 64 (l + i)) 1 = Some [nth (Z.to_nat i) bs (Z_to_bv 8 0)].
Proof.
  intros m l bs i HB Hl Hn Hi. apply (bytes_at_rdn SEGS m (l + i) [nth (Z.to_nat i) bs (Z_to_bv 8 0)]); [lia | cbn; lia |].
  intros j Hj. cbn [length] in Hj. assert (j = 0%Z) by lia. subst j. rewrite Z.add_0_r. cbn [nth Z.to_nat]. apply HB. exact Hi.
Qed.

Lemma nth_app_nz : forall (bs : list byte) (i : Z), Forall (fun b => b <> Z_to_bv 8 0) bs -> (0 <= i < Z.of_nat (length bs))%Z ->
  nth (Z.to_nat i) (bs ++ [Z_to_bv 8 0]) (Z_to_bv 8 0) <> Z_to_bv 8 0.
Proof.
  intros bs i NZ Hi. rewrite app_nth1 by lia. rewrite Forall_forall in NZ. apply NZ. apply nth_In. lia.
Qed.
Lemma nth_app_last : forall (bs : list byte), nth (length bs) (bs ++ [Z_to_bv 8 0]) (Z_to_bv 8 0) = Z_to_bv 8 0.
Proof. intros bs. rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity. Qed.
Lemma byte_nz_u : forall b : byte, b <> Z_to_bv 8 0 -> (u b <> 0)%Z.
Proof. intros b H E. apply H. apply byte_u0. exact E. Qed.

Section StrlenSegs.
Variable rom : word -> option byte.

  (* [comment removed for export] *)
  Lemma sl_A : forall regs m (s : Z) (b0 : byte),
    (1 <= s)%Z -> (s + 8 < 2 ^ 64)%Z -> (s mod 8 <> 0)%Z -> rdn SEGS m (Z_to_bv 64 s) 1 = Some [b0] -> (u b0 <> 0)%Z ->
    getr regs 10 = Z_to_bv 64 s ->
    exists regs',
      msteps SEGS (mkst regs (0x2a4fc : word) m rom) (mkst regs' (0x2a518 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 s /\ getr regs' 11 = Z_to_bv 64 s /\ getr regs' 12 = Z_to_bv 64 (s + 1) /\ getr regs' 1 = getr regs 1
      /\ regs_agree (fun r => In r [11; 12; 13; 14; 15; 16]%list) regs regs'.
  Proof.
    intros regs m s b0 Hs Hs8 Hal R0 N0 H10. pose proof (u8_range b0) as U0.
    pose proof (Z.mod_pos_bound s 8 ltac:(lia)) as M8.
    eexists. split.
    - sn F_29fc0 D_29fc0. fixv (Z_to_bv 64 (s mod 8)) ltac:(pin; rewrite andi_7, u_Z2bv by lia; reflexivity).
      sn F_29fc4 D_29fc4.
      stepb_ft F_29fc8 D_29fc8 ltac:(condZm).
      stepLBU F_29fcc D_29fcc b0 ltac:(addr_norm; exact R0).
      stepb_ft F_29fd0 D_29fd0 ltac:(condZ).
      zv F_29fd4 D_29fd4 (Z_to_bv 64 (s + 1)).
      sn F_29fd8 D_29fd8.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma sl_P_cont : forall regs m (q : Z) (b : byte),
    (1 <= q)%Z -> (q + 8 < 2 ^ 64)%Z -> ((q + 1) mod 8 <> 0)%Z -> rdn SEGS m (Z_to_bv 64 (q + 1)) 1 = Some [b] -> (u b <> 0)%Z ->
    getr regs 11 = Z_to_bv 64 q -> getr regs 12 = Z_to_bv 64 (q + 1) ->
    exists regs',
      msteps SEGS (mkst regs (0x2a518 : word) m rom) (mkst regs' (0x2a518 : word) m rom)
      /\ getr regs' 11 = Z_to_bv 64 (q + 1) /\ getr regs' 12 = Z_to_bv 64 (q + 1 + 1) /\ getr regs' 10 = getr regs 10 /\ getr regs' 1 = getr regs 1
      /\ regs_agree (fun r => In r [11; 12; 13; 14; 15; 16]%list) regs regs'.
  Proof.
    intros regs m q b Hq Hq8 Hal Rb Nb H11 H12. pose proof (u8_range b) as Ub.
    pose proof (Z.mod_pos_bound (q + 1) 8 ltac:(lia)) as M8.
    eexists. split.
    - zv F_29fdc D_29fdc (Z_to_bv 64 (q + 1)).
      sn F_29fe0 D_29fe0. fixv (Z_to_bv 64 ((q + 1) mod 8)) ltac:(rewrite andi_7, u_Z2bv by lia; reflexivity).
      stepb_ft F_29fe4 D_29fe4 ltac:(condZm).
      stepLBU F_29fe8 D_29fe8 b ltac:(addr_norm; exact Rb).
      zv F_29fec D_29fec (Z_to_bv 64 (q + 1 + 1)).
      zv F_29ff0 D_29ff0 (Z_to_bv 64 (q + 1)).
      stepb_tk F_29ff4 D_29ff4 ltac:(condZ).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma sl_P_W : forall regs m (q : Z) (wd : list byte),
    (1 <= q)%Z -> (q + 16 < 2 ^ 64)%Z -> ((q + 1) mod 8 = 0)%Z ->
    rdn SEGS m (Z_to_bv 64 (q + 1)) 8 = Some wd -> strlen_stop (Z_to_bv 64 (bytes_le_to_Z wd)) ->
    rdn SEGS m (Z_to_bv 64 0x11758) 8 = Some (Z_to_le_bytes 8 SL_C1) -> rdn SEGS m (Z_to_bv 64 0x11748) 8 = Some (Z_to_le_bytes 8 SL_C2) ->
    getr regs 11 = Z_to_bv 64 q -> getr regs 12 = Z_to_bv 64 (q + 1) ->
    exists regs',
      msteps SEGS (mkst regs (0x2a518 : word) m rom) (mkst regs' (0x2a56c : word) m rom)
      /\ getr regs' 11 = Z_to_bv 64 q /\ getr regs' 12 = Z_to_bv 64 (q + 1) /\ getr regs' 10 = getr regs 10 /\ getr regs' 1 = getr regs 1
      /\ regs_agree (fun r => In r [11; 12; 13; 14; 15; 16]%list) regs regs'.
  Proof.
    intros regs m q wd Hq Hq16 Hal Rw STOP RC1 RC2 H11 H12. unfold strlen_stop in STOP.
    assert (Lwd : length wd = 8%nat) by (apply rdn_length in Rw; exact Rw).
    eexists. split.
    - zv F_29fdc D_29fdc (Z_to_bv 64 (q + 1)).
      sn F_29fe0 D_29fe0. fixv (Z_to_bv 64 0) ltac:(rewrite andi_7, u_Z2bv by lia; f_equal; lia).
      stepb_tk F_29fe4 D_29fe4 ltac:(condZ).
      sn F_29ffc D_29ffc. sn F_2a000 D_2a000.
      stepLD F_2a004 D_2a004 (Z_to_le_bytes 8 SL_C1) (Z_to_bv 64 SL_C1) ltac:(addr_norm; exact RC1) ltac:(apply lez8; unfold SL_C1; lia).
      stepLD F_2a008 D_2a008 (Z_to_le_bytes 8 SL_C2) (Z_to_bv 64 SL_C2) ltac:(addr_norm; exact RC2) ltac:(apply lez8; unfold SL_C2; lia).
      zv F_2a00c D_2a00c (Z_to_bv 64 (q + 1 - 9)).
      zv F_2a010 D_2a010 (Z_to_bv 64 (q + 1 - 8)).
      stepLD F_2a014 D_2a014 wd (Z_to_bv 64 (bytes_le_to_Z wd)) ltac:(rewrite zbv_addi; replace (q + 1 - 8 + 8)%Z with (q + 1)%Z by lia; exact Rw)
        ltac:(rewrite u_Z2bv; [reflexivity | apply bytes_le_to_Z_nonneg | pose proof (bytes_le_to_Z_bound wd); rewrite Lwd in *; lia]).
      zv F_2a018 D_2a018 (Z_to_bv 64 (q + 1)).
      sn F_2a01c D_2a01c. sn F_2a020 D_2a020. sn F_2a024 D_2a024.
      zv F_2a028 D_2a028 (Z_to_bv 64 q).
      stepb_ft F_2a02c D_2a02c ltac:(pin; exact STOP).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  (* [comment removed for export] *)
  Lemma sl_T_cont : forall regs m (t : Z) (b : byte),
    (1 <= t)%Z -> (t + 8 < 2 ^ 64)%Z -> rdn SEGS m (Z_to_bv 64 t) 1 = Some [b] -> (u b <> 0)%Z ->
    getr regs 11 = Z_to_bv 64 (t - 1) -> getr regs 12 = Z_to_bv 64 t ->
    exists regs',
      msteps SEGS (mkst regs (0x2a56c : word) m rom) (mkst regs' (0x2a56c : word) m rom)
      /\ getr regs' 11 = Z_to_bv 64 (t + 1 - 1) /\ getr regs' 12 = Z_to_bv 64 (t + 1) /\ getr regs' 10 = getr regs 10 /\ getr regs' 1 = getr regs 1
      /\ regs_agree (fun r => In r [11; 12; 13; 14; 15; 16]%list) regs regs'.
  Proof.
    intros regs m t b Ht Ht8 Rb Nb H11 H12. pose proof (u8_range b) as Ub.
    eexists. split.
    - stepLBU F_2a030 D_2a030 b ltac:(addr_norm; exact Rb).
      zv F_2a034 D_2a034 (Z_to_bv 64 (t + 1)).
      zv F_2a038 D_2a038 (Z_to_bv 64 (t + 1 - 1)).
      stepb_tk F_2a03c D_2a03c ltac:(condZ).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma sl_T_exit : forall regs m (s t : Z) (ret : word),
    (1 <= s)%Z -> (s <= t)%Z -> (t + 8 < 2 ^ 64)%Z -> rdn SEGS m (Z_to_bv 64 t) 1 = Some [Z_to_bv 8 0] ->
    getr regs 1 = ret -> ret_ok ret -> getr regs 10 = Z_to_bv 64 s -> getr regs 11 = Z_to_bv 64 (t - 1) -> getr regs 12 = Z_to_bv 64 t ->
    exists regs',
      msteps SEGS (mkst regs (0x2a56c : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 10 = Z_to_bv 64 (t - s)
      /\ regs_agree (fun r => In r [10; 11; 12; 13; 14; 15; 16]%list) regs regs'.
  Proof.
    intros regs m s t ret Hs Hst Ht8 Rb H1 Hret H10 H11 H12.
    eexists. split.
    - stepLBU F_2a030 D_2a030 (Z_to_bv 8 0) ltac:(addr_norm; exact Rb).
      zv F_2a034 D_2a034 (Z_to_bv 64 (t + 1)).
      zv F_2a038 D_2a038 (Z_to_bv 64 t).
      stepb_ft F_2a03c D_2a03c ltac:(condZ).
      zv F_2a040 D_2a040 (Z_to_bv 64 (t - s)).
      stepret F_2a044 D_2a044 ret ltac:(exact H1).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma sl_P_loop : forall (n : nat) regs m (s p k : Z) (bs wd : list byte),
    rd_str SEGS m s (bs ++ [Z_to_bv 8 0]) -> Forall (fun b => b <> Z_to_bv 8 0) bs ->
    (1 <= s)%Z -> (s + Z.of_nat (length bs) + 16 < 2 ^ 64)%Z -> (1 <= p <= 7)%Z -> ((s + p) mod 8 = 0)%Z -> (p <= Z.of_nat (length bs))%Z ->
    (Z.of_nat n = p - 1 - k)%Z -> (0 <= k)%Z ->
    rdn SEGS m (Z_to_bv 64 (s + p)) 8 = Some wd -> strlen_stop (Z_to_bv 64 (bytes_le_to_Z wd)) ->
    rdn SEGS m (Z_to_bv 64 0x11758) 8 = Some (Z_to_le_bytes 8 SL_C1) -> rdn SEGS m (Z_to_bv 64 0x11748) 8 = Some (Z_to_le_bytes 8 SL_C2) ->
    getr regs 11 = Z_to_bv 64 (s + k) -> getr regs 12 = Z_to_bv 64 (s + k + 1) ->
    exists regs',
      msteps SEGS (mkst regs (0x2a518 : word) m rom) (mkst regs' (0x2a56c : word) m rom)
      /\ getr regs' 11 = Z_to_bv 64 (s + p - 1) /\ getr regs' 12 = Z_to_bv 64 (s + p) /\ getr regs' 10 = getr regs 10 /\ getr regs' 1 = getr regs 1
      /\ regs_agree (fun r => In r [11; 12; 13; 14; 15; 16]%list) regs regs'.
  Proof.
    induction n as [|n IH]; intros regs m s p k bs wd HB NZ Hs Hlen Hp Hal Hpl Hn Hk Rw STOP RC1 RC2 H11 H12.
    - assert (Ek : (s + k + 1 = s + p)%Z) by lia.
      destruct (sl_P_W regs m (s + k)%Z wd ltac:(lia) ltac:(lia) ltac:(rewrite Ek; exact Hal) ltac:(rewrite Ek; exact Rw) STOP RC1 RC2 H11 H12)
        as (r1 & RUN1 & Q11 & Q12 & Q10 & Q1 & AG1).
      exists r1. split; [exact RUN1|]. split; [rewrite Q11; f_equal; lia|]. split; [rewrite Q12; f_equal; lia|]. split; [exact Q10|]. split; [exact Q1 | exact AG1].
    - assert (Hnal : ((s + k + 1) mod 8 <> 0)%Z).
      { intros E. pose proof (Z.div_mod (s + k + 1) 8 ltac:(lia)) as D1. pose proof (Z.div_mod (s + p) 8 ltac:(lia)) as D2. rewrite E in D1. rewrite Hal in D2. lia. }
      assert (LA : Z.of_nat (length (bs ++ [Z_to_bv 8 0])) = (Z.of_nat (length bs) + 1)%Z) by (rewrite length_app; cbn [length]; lia).
      pose proof (HB (k + 1)%Z ltac:(lia)) as Rb.
      pose proof (byte_nz_u _ (nth_app_nz bs (k + 1)%Z NZ ltac:(lia))) as Nb.
      replace (s + (k + 1))%Z with (s + k + 1)%Z in Rb by lia.
      destruct (sl_P_cont regs m (s + k)%Z _ ltac:(lia) ltac:(lia) Hnal Rb Nb H11 H12) as (r1 & RUN1 & Q11 & Q12 & Q10 & Q1 & AG1).
      destruct (IH r1 m s p (k + 1)%Z bs wd HB NZ Hs Hlen Hp Hal Hpl ltac:(lia) ltac:(lia) Rw STOP RC1 RC2
                  ltac:(rewrite Q11; f_equal; lia) ltac:(rewrite Q12; f_equal; lia)) as (r2 & RUN2 & P11 & P12 & P10 & P1 & AG2).
      exists r2. split; [exact (msteps_trans SEGS _ _ _ RUN1 RUN2)|]. split; [exact P11|]. split; [exact P12|].
      split; [rewrite P10; exact Q10|]. split; [rewrite P1; exact Q1 | exact (regs_agree_trans _ _ _ _ AG1 AG2)].
  Qed.

  (* [comment removed for export] *)
  Lemma sl_T_loop : forall (n : nat) regs m (s j : Z) (bs : list byte) (ret : word),
    rd_str SEGS m s (bs ++ [Z_to_bv 8 0]) -> Forall (fun b => b <> Z_to_bv 8 0) bs ->
    (1 <= s)%Z -> (s + Z.of_nat (length bs) + 16 < 2 ^ 64)%Z -> (Z.of_nat n = Z.of_nat (length bs) - j)%Z -> (0 <= j)%Z ->
    getr regs 1 = ret -> ret_ok ret -> getr regs 10 = Z_to_bv 64 s -> getr regs 11 = Z_to_bv 64 (s + j - 1) -> getr regs 12 = Z_to_bv 64 (s + j) ->
    exists regs',
      msteps SEGS (mkst regs (0x2a56c : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 10 = Z_to_bv 64 (Z.of_nat (length bs))
      /\ regs_agree (fun r => In r [10; 11; 12; 13; 14; 15; 16]%list) regs regs'.
  Proof.
    induction n as [|n IH]; intros regs m s j bs ret HB NZ Hs Hlen Hn Hj H1 Hret H10 H11 H12;
      assert (LA : Z.of_nat (length (bs ++ [Z_to_bv 8 0])) = (Z.of_nat (length bs) + 1)%Z) by (rewrite length_app; cbn [length]; lia);
      pose proof (HB j ltac:(lia)) as Rb.
    - assert (Ej : j = Z.of_nat (length bs)) by lia. rewrite Ej, Nat2Z.id, nth_app_last in Rb. rewrite <- Ej in Rb.
      destruct (sl_T_exit regs m s (s + j)%Z ret Hs ltac:(lia) ltac:(lia) Rb H1 Hret H10 H11 H12) as (r1 & RUN1 & Q10 & AG1).
      exists r1. split; [exact RUN1|]. split; [rewrite Q10; f_equal; lia | exact AG1].
    - pose proof (byte_nz_u _ (nth_app_nz bs j NZ ltac:(lia))) as Nb.
      destruct (sl_T_cont regs m (s + j)%Z _ ltac:(lia) ltac:(lia) Rb Nb H11 H12) as (r1 & RUN1 & Q11 & Q12 & Q10 & Q1 & AG1).
      destruct (IH r1 m s (j + 1)%Z bs ret HB NZ Hs Hlen ltac:(lia) ltac:(lia) ltac:(rewrite Q1; exact H1) Hret ltac:(rewrite Q10; exact H10)
                  ltac:(rewrite Q11; f_equal; lia) ltac:(rewrite Q12; f_equal; lia)) as (r2 & RUN2 & P10 & AG2).
      exists r2. split; [exact (msteps_trans SEGS _ _ _ RUN1 RUN2)|]. split; [exact P10|].
      eapply regs_agree_trans; [| exact AG2]. eapply regs_agree_mono; [| exact AG1]. intros r Hr. cbn [In] in *. tauto.
  Qed.

  (* [comment removed for export] *)
  Lemma strlen_run_W : forall regs m (s p : Z) (bs wd : list byte) (ret : word),
    rd_str SEGS m s (bs ++ [Z_to_bv 8 0]) -> Forall (fun b => b <> Z_to_bv 8 0) bs ->
    (1 <= s)%Z -> (s + Z.of_nat (length bs) + 16 < 2 ^ 64)%Z -> (1 <= p <= 7)%Z -> ((s + p) mod 8 = 0)%Z -> (p <= Z.of_nat (length bs))%Z ->
    rdn SEGS m (Z_to_bv 64 (s + p)) 8 = Some wd -> strlen_stop (Z_to_bv 64 (bytes_le_to_Z wd)) ->
    rdn SEGS m (Z_to_bv 64 0x11758) 8 = Some (Z_to_le_bytes 8 SL_C1) -> rdn SEGS m (Z_to_bv 64 0x11748) 8 = Some (Z_to_le_bytes 8 SL_C2) ->
    getr regs 1 = ret -> ret_ok ret -> getr regs 10 = Z_to_bv 64 s ->
    exists regs',
      msteps SEGS (mkst regs (0x2a4fc : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 10 = Z_to_bv 64 (Z.of_nat (length bs))
      /\ regs_agree (fun r => In r [10; 11; 12; 13; 14; 15; 16]%list) regs regs'.
  Proof.
    intros regs m s p bs wd ret HB NZ Hs Hlen Hp Hal Hpl Rw STOP RC1 RC2 H1 Hret H10.
    assert (LA : Z.of_nat (length (bs ++ [Z_to_bv 8 0])) = (Z.of_nat (length bs) + 1)%Z) by (rewrite length_app; cbn [length]; lia).
    assert (Hnal : (s mod 8 <> 0)%Z).
    { intros E. pose proof (Z.div_mod s 8 ltac:(lia)) as D1. pose proof (Z.div_mod (s + p) 8 ltac:(lia)) as D2. rewrite E in D1. rewrite Hal in D2. lia. }
    pose proof (HB 0%Z ltac:(lia)) as R0. rewrite Z.add_0_r in R0.
    pose proof (byte_nz_u _ (nth_app_nz bs 0%Z NZ ltac:(lia))) as N0.
    destruct (sl_A regs m s _ Hs ltac:(lia) Hnal R0 N0 H10) as (r1 & RUN1 & Q10 & Q11 & Q12 & Q1 & AG1).
    destruct (sl_P_loop (Z.to_nat (p - 1)) r1 m s p 0%Z bs wd HB NZ Hs Hlen Hp Hal Hpl ltac:(lia) ltac:(lia) Rw STOP RC1 RC2
                ltac:(rewrite Q11; f_equal; lia) ltac:(rewrite Q12; f_equal; lia)) as (r2 & RUN2 & P11 & P12 & P10 & P1 & AG2).
    destruct (sl_T_loop (Z.to_nat (Z.of_nat (length bs) - p)) r2 m s p bs ret HB NZ Hs Hlen ltac:(lia) ltac:(lia)
                ltac:(rewrite P1, Q1; exact H1) Hret ltac:(rewrite P10; exact Q10) P11 P12) as (r3 & RUN3 & T10 & AG3).
    exists r3. split; [exact (msteps_trans SEGS _ _ _ RUN1 (msteps_trans SEGS _ _ _ RUN2 RUN3))|]. split; [exact T10|].
    eapply regs_agree_trans; [| exact AG3]. eapply regs_agree_mono; [| exact (regs_agree_trans _ _ _ _ AG1 AG2)]. intros r Hr. cbn [In] in *. tauto.
  Qed.
End StrlenSegs.

End SelSegs.
End O10LeptSelSegs.
