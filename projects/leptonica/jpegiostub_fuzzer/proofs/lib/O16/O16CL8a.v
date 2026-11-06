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
From OSSVerify.leptonica.jpegiostub_fuzzer.images Require Plain.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common Require PropExec.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common Require CatExec.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common Require CatSim.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common Require StepTac.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common Require Hoare.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common Require ShapeAlg.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common Require AllocIface.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common Require PureModel.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common Require VmLedger.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common Require StoreOk.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common Require MemSplit.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common Require RefMemcpyLib.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common Require StartupTac.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common Require WalkTac.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Mallocng Require AllocBase.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Mallocng Require AllocCalloc.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Mallocng Require AllocSure.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica Require SumWalkTac.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica Require SumSpecs.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica Require WalksLib.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica Require W2Lib.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica Require LeptDefs.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica Require LeptStructs.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.O16 Require O16LeptStderr.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.O16 Require O16LeptBase.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.O16 Require O16CL7a.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica Require LeptRoom.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Reloc Require Reloc.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica Require RelocLept.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica.OL Require LeptCmap.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.O16 Require O16Kit.
Module O16LeptCmap.
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
Import OSSVerify.leptonica.jpegiostub_fuzzer.images.Plain.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.StepTac.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.AllocIface.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.PureModel.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.VmLedger.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.StoreOk.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.MemSplit.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.RefMemcpyLib.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.StartupTac.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.WalkTac.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Mallocng.AllocBase.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Mallocng.AllocSure.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica.SumWalkTac.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica.SumSpecs.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica.WalksLib.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica.W2Lib.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica.LeptDefs.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica.LeptStructs.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.O16.O16LeptStderr.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.O16.O16LeptBase.
Import O16CL7a.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica.LeptRoom.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Reloc.Reloc.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica.RelocLept.
Import O16Kit.
(* [comment removed for export] *)










Import O16CL7a.O16LeptErr.





Import O16Kit.O16Reloc. Import O16Kit.O16RelocCode. Import O16Kit.O16RelocSites. Import O16Kit.O16RelocImg. Import O16Kit.O16RelocOL.
Import O16Kit.O16RelocMusl. Import O16Kit.O16LeptEnv.
Import O16CL7a.O16LeptG.
Import ListNotations.
Open Scope bv_scope.

Lemma sllw_1 : forall d, (d = 1 \/ d = 2 \/ d = 4 \/ d = 8)%Z -> v_sllw (Z_to_bv 64 1) (Z_to_bv 64 d) = Z_to_bv 64 (2 ^ d).
Proof. rl_tail (@LeptCmap.sllw_1). Qed.

Section Cmap.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LL16} {P16 : O16Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
Theorem pixcmapDestroy_W : forall C A m md regs (s pp cm : Z) (cv : cmapv) (k : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 32 + ALLOC_STACK <= s)%Z -> (s <= pp)%Z -> (pp + 8 <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x2fb50 ->
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
  realizes SEGS (mkCfg (mkst regs (0x14510 : word) m al_rom) md) S.
Proof. rl_tail (@LeptCmap.pixcmapDestroy_W fx o16_reloc o16_code_ol o16_sites_ol o16_lept AL CL ASR PINS (o16_pinsG P16)). Qed.

End Cmap.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).      (* [comment removed for export] *)
End O16LeptCmap.

From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica Require LibAtomic.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica Require LeptArith.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica Require LeptArith2.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica.OL Require LeptDeserA.
Module O16LeptDeserA.
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
Import OSSVerify.leptonica.jpegiostub_fuzzer.images.Plain.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.StepTac.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.AllocIface.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.PureModel.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.VmLedger.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.StoreOk.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.MemSplit.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.RefMemcpyLib.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.StartupTac.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.WalkTac.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Mallocng.AllocBase.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Mallocng.AllocSure.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica.SumWalkTac.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica.SumSpecs.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica.WalksLib.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica.W2Lib.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica.LibAtomic.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica.LeptDefs.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica.LeptStructs.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica.LeptArith.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica.LeptArith2.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.O16.O16LeptStderr.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.O16.O16LeptBase.
Import O16CL7a.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica.LeptRoom.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Reloc.Reloc.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica.RelocLept.
Import O16Kit.
(* [comment removed for export] *)










Import O16CL7a.O16LeptErr.





Import O16Kit.O16Reloc. Import O16Kit.O16RelocCode. Import O16Kit.O16RelocSites. Import O16Kit.O16RelocImg. Import O16Kit.O16RelocOL.
Import O16Kit.O16RelocMusl. Import O16Kit.O16LeptEnv.
Import O16CL7a.O16LeptG.
Import ListNotations.
Open Scope bv_scope.

Section DeserA.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LL16} {P16 : O16Pins}.
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
      msteps SEGS (mkst regs (0x14c90 : word) m rom) (mkst regs' (0x14cd0 : word) (FR12 m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 112) /\ getr regs' 10 = Z_to_bv 64 dp /\ getr regs' 11 = Z_to_bv 64 nb
      /\ getr regs' 12 = Z_to_bv 64 18446744071562067995 /\ getr regs' 13 = Z_to_bv 64 (nb + 18446744071562067968)
      /\ regs_agree (fun r => In r [2; 12; 13]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_A0 fx o16_reloc o16_code_ol rom). Qed.

Lemma pd_A1 : forall regs m (nb : Z),
    (28 <= nb < 2 ^ 31)%Z -> getr regs 12 = Z_to_bv 64 18446744071562067995 -> getr regs 13 = Z_to_bv 64 (nb + 18446744071562067968) ->
    exists regs', msteps SEGS (mkst regs (0x14cd0 : word) m rom) (mkst regs' (0x14d30 : word) m rom) /\ regs_agree (fun r => False) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_A1 fx o16_reloc o16_code_ol rom). Qed.

Lemma pd_A2 : forall regs m (nb : Z),
    (0 <= nb < 28)%Z -> getr regs 12 = Z_to_bv 64 18446744071562067995 -> getr regs 13 = Z_to_bv 64 (nb + 18446744071562067968) ->
    getr regs 11 = Z_to_bv 64 nb ->
    rdn SEGS m (Z_to_bv 64 0x1e780) 8 = Some (Z_to_le_bytes 8 0x1f7f0) -> rdn SEGS m (Z_to_bv 64 0x1f7f0) 4 = Some (Z_to_le_bytes 4 3) ->
    exists regs',
      msteps SEGS (mkst regs (0x14cd0 : word) m rom) (mkst regs' (0x1371c : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 0x106fa /\ getr regs' 11 = Z_to_bv 64 0x105cb /\ getr regs' 12 = Z_to_bv 64 nb /\ getr regs' 1 = Z_to_bv 64 0x14d04
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_A2 fx o16_reloc o16_code_ol o16_sites_ol rom). Qed.

Lemma pd_B : forall regs m (dp : Z) (b0 b1 b2 b3 : byte),
    (1 <= dp)%Z -> (dp + 4 <= 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 dp) 1 = Some [b0] -> rdn SEGS m (Z_to_bv 64 (dp + 1)) 1 = Some [b1] ->
    rdn SEGS m (Z_to_bv 64 (dp + 2)) 1 = Some [b2] -> rdn SEGS m (Z_to_bv 64 (dp + 3)) 1 = Some [b3] ->
    u b0 = 115%Z -> u b1 = 112%Z -> u b2 = 105%Z -> u b3 = 120%Z ->
    getr regs 10 = Z_to_bv 64 dp ->
    exists regs', msteps SEGS (mkst regs (0x14d30 : word) m rom) (mkst regs' (0x14d60 : word) m rom)
      /\ regs_agree (fun r => In r [12; 13]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_B fx o16_reloc o16_code_ol rom). Qed.

Lemma pd_Bbad : forall regs m (dp : Z) (b0 b1 b2 b3 : byte),
    (1 <= dp)%Z -> (dp + 4 <= 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 dp) 1 = Some [b0] -> rdn SEGS m (Z_to_bv 64 (dp + 1)) 1 = Some [b1] ->
    rdn SEGS m (Z_to_bv 64 (dp + 2)) 1 = Some [b2] -> rdn SEGS m (Z_to_bv 64 (dp + 3)) 1 = Some [b3] ->
    ~ (u b0 = 115 /\ u b1 = 112 /\ u b2 = 105 /\ u b3 = 120)%Z ->
    getr regs 10 = Z_to_bv 64 dp ->
    exists regs', msteps SEGS (mkst regs (0x14d30 : word) m rom) (mkst regs' (0x14d9c : word) m rom)
      /\ regs_agree (fun r => In r [12; 13]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_Bbad fx o16_reloc o16_code_ol rom). Qed.

Lemma pd_C : forall regs m (dp wr : Z) bs4,
    (1 <= dp)%Z -> (dp + 28 <= 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (dp + 4)) 4 = Some bs4 -> bytes_le_to_Z bs4 = wr -> (1 <= wr <= 1000000)%Z ->
    getr regs 10 = Z_to_bv 64 dp ->
    exists regs', msteps SEGS (mkst regs (0x14d60 : word) m rom) (mkst regs' (0x14df8 : word) m rom)
      /\ getr regs' 9 = Z_to_bv 64 wr /\ getr regs' 12 = Z_to_bv 64 18446744073708551615
      /\ regs_agree (fun r => In r [9; 12; 13]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_C fx o16_reloc o16_code_ol rom). Qed.

Lemma pd_Cbad : forall regs m (dp wr : Z) bs4,
    (1 <= dp)%Z -> (dp + 28 <= 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (dp + 4)) 4 = Some bs4 -> bytes_le_to_Z bs4 = wr -> (0 <= wr < 2 ^ 32)%Z -> ~ (1 <= wr <= 1000000)%Z ->
    getr regs 10 = Z_to_bv 64 dp ->
    exists regs', msteps SEGS (mkst regs (0x14d60 : word) m rom) (mkst regs' (0x14d74 : word) m rom)
      /\ regs_agree (fun r => In r [9; 12; 13]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_Cbad fx o16_reloc o16_code_ol rom). Qed.

Lemma pd_D : forall regs m (dp hr : Z) bs8,
    (1 <= dp)%Z -> (dp + 28 <= 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (dp + 8)) 4 = Some bs8 -> bytes_le_to_Z bs8 = hr -> (1 <= hr <= 1000000)%Z ->
    getr regs 10 = Z_to_bv 64 dp -> getr regs 12 = Z_to_bv 64 18446744073708551615 ->
    exists regs', msteps SEGS (mkst regs (0x14df8 : word) m rom) (mkst regs' (0x14e2c : word) m rom)
      /\ getr regs' 18 = Z_to_bv 64 hr /\ regs_agree (fun r => In r [18; 13]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_D fx o16_reloc o16_code_ol rom). Qed.

Lemma pd_Dbad : forall regs m (dp hr : Z) bs8,
    (1 <= dp)%Z -> (dp + 28 <= 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (dp + 8)) 4 = Some bs8 -> bytes_le_to_Z bs8 = hr -> (0 <= hr < 2 ^ 32)%Z -> ~ (1 <= hr <= 1000000)%Z ->
    getr regs 10 = Z_to_bv 64 dp -> getr regs 12 = Z_to_bv 64 18446744073708551615 ->
    exists regs', msteps SEGS (mkst regs (0x14df8 : word) m rom) (mkst regs' (0x14e04 : word) m rom)
      /\ regs_agree (fun r => In r [18; 13]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_Dbad fx o16_reloc o16_code_ol rom). Qed.

Lemma pd_E : forall regs m (wr hr : Z),
    (1 <= wr <= 1000000)%Z -> (1 <= hr <= 1000000)%Z -> (wr * hr <= 400000000)%Z ->
    getr regs 9 = Z_to_bv 64 wr -> getr regs 18 = Z_to_bv 64 hr ->
    exists regs', msteps SEGS (mkst regs (0x14e2c : word) m rom) (mkst regs' (0x14e64 : word) m rom)
      /\ regs_agree (fun r => In r [12; 13]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_E fx o16_reloc o16_code_ol rom). Qed.

Lemma pd_Ebad : forall regs m (wr hr : Z),
    (1 <= wr <= 1000000)%Z -> (1 <= hr <= 1000000)%Z -> (400000000 < wr * hr)%Z ->
    getr regs 9 = Z_to_bv 64 wr -> getr regs 18 = Z_to_bv 64 hr ->
    exists regs', msteps SEGS (mkst regs (0x14e2c : word) m rom) (mkst regs' (0x14e3c : word) m rom)
      /\ regs_agree (fun r => In r [12; 13]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_Ebad fx o16_reloc o16_code_ol rom). Qed.

Lemma pd_F : forall regs m (dp nb ncr q dr wr hr : Z) bs20 bs12,
    (1 <= dp)%Z -> (dp + 28 <= 2 ^ 64)%Z -> (28 <= nb < 2 ^ 31)%Z -> q = (nb / 4)%Z ->
    rdn SEGS m (Z_to_bv 64 (dp + 20)) 4 = Some bs20 -> bytes_le_to_Z bs20 = ncr -> (0 <= ncr <= 256)%Z -> (ncr + 7 < q)%Z ->
    rdn SEGS m (Z_to_bv 64 (dp + 12)) 4 = Some bs12 -> bytes_le_to_Z bs12 = dr -> (0 <= dr < 2 ^ 32)%Z ->
    (0 <= wr < 2 ^ 64)%Z -> (0 <= hr < 2 ^ 64)%Z ->
    getr regs 10 = Z_to_bv 64 dp -> getr regs 11 = Z_to_bv 64 nb -> getr regs 9 = Z_to_bv 64 wr -> getr regs 18 = Z_to_bv 64 hr ->
    exists regs', msteps SEGS (mkst regs (0x14e64 : word) m rom) (mkst regs' (0x139e4 : word) m rom)
      /\ getr regs' 23 = Z_to_bv 64 ncr /\ getr regs' 8 = Z_to_bv 64 nb /\ getr regs' 25 = Z_to_bv 64 dp
      /\ getr regs' 20 = Z_to_bv 64 (zx (sw32 dr))
      /\ getr regs' 10 = Z_to_bv 64 wr /\ getr regs' 11 = Z_to_bv 64 hr /\ getr regs' 12 = Z_to_bv 64 (zx (sw32 dr)) /\ getr regs' 1 = Z_to_bv 64 0x14e98
      /\ regs_agree (fun r => In r [1; 8; 10; 11; 12; 13; 20; 23; 25]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_F fx o16_reloc o16_code_ol o16_sites_ol rom). Qed.

Lemma pd_Fbad : forall regs m (dp nb ncr q : Z) bs20,
    (1 <= dp)%Z -> (dp + 28 <= 2 ^ 64)%Z -> (28 <= nb < 2 ^ 31)%Z -> q = (nb / 4)%Z ->
    rdn SEGS m (Z_to_bv 64 (dp + 20)) 4 = Some bs20 -> bytes_le_to_Z bs20 = ncr -> (0 <= ncr < 2 ^ 32)%Z -> ~ (ncr <= 256 /\ ncr + 7 < q)%Z ->
    getr regs 10 = Z_to_bv 64 dp -> getr regs 11 = Z_to_bv 64 nb ->
    exists regs', msteps SEGS (mkst regs (0x14e64 : word) m rom) (mkst regs' (0x14f4c : word) m rom)
      /\ regs_agree (fun r => In r [12; 13; 23]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_Fbad fx o16_reloc o16_code_ol rom). Qed.

Definition et_leaves : list (Z * Z) :=
    [(0x14d9c, 0x1071d); (0x14d74, 0x10935); (0x14e04, 0x10340); (0x14e3c, 0x10316); (0x14f4c, 0x10764); (0x14f74, 0x1047c)]%Z.
Lemma pd_ET : forall pc msg regs m,
    In (pc, msg) et_leaves ->
    rdn SEGS m (Z_to_bv 64 0x1e780) 8 = Some (Z_to_le_bytes 8 0x1f7f0) -> rdn SEGS m (Z_to_bv 64 0x1f7f0) 4 = Some (Z_to_le_bytes 4 3) ->
    exists regs', msteps SEGS (mkst regs (Z_to_bv 64 pc) m rom) (mkst regs' (0x14dc0 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 msg /\ getr regs' 11 = Z_to_bv 64 0x105cb
      /\ regs_agree (fun r => In r [10; 11]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_ET fx o16_reloc o16_code_ol o16_sites_ol rom). Qed.

Definition ej_leaves : list (Z * Z) := [(0x14fd4, 0x107cc); (0x1500c, 0x10a26); (0x15074, 0x103e3)]%Z.
Lemma pd_EJ : forall pc msg regs m,
    In (pc, msg) ej_leaves ->
    rdn SEGS m (Z_to_bv 64 0x1e780) 8 = Some (Z_to_le_bytes 8 0x1f7f0) -> rdn SEGS m (Z_to_bv 64 0x1f7f0) 4 = Some (Z_to_le_bytes 4 3) ->
    exists regs', msteps SEGS (mkst regs (Z_to_bv 64 pc) m rom) (mkst regs' (0x137b8 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 msg /\ getr regs' 11 = Z_to_bv 64 0x105cb /\ getr regs' 12 = Z_to_bv 64 0 /\ getr regs' 1 = Z_to_bv 64 0x150a0
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_EJ fx o16_reloc o16_code_ol o16_sites_ol rom). Qed.

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
    exists regs', msteps SEGS (mkst regs (0x14dc0 : word) m rom) (mkst regs' (0x137b8 : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 12 = Z_to_bv 64 0
      /\ getr regs' 8 = sv 8%nat /\ getr regs' 9 = sv 9%nat /\ getr regs' 18 = sv 18%nat /\ getr regs' 19 = sv 19%nat
      /\ getr regs' 20 = sv 20%nat /\ getr regs' 21 = sv 21%nat /\ getr regs' 22 = sv 22%nat /\ getr regs' 23 = sv 23%nat
      /\ getr regs' 24 = sv 24%nat /\ getr regs' 25 = sv 25%nat
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 12; 18; 19; 20; 21; 22; 23; 24; 25]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_X50 fx o16_reloc o16_code_ol o16_sites_ol rom). Qed.

Lemma pd_RET : forall regs m (s : Z) (ret : word) (sv : nat -> word),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret -> pd_cells m s ret sv -> getr regs 2 = Z_to_bv 64 (s - 112) ->
    exists regs', msteps SEGS (mkst regs (0x150a8 : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret
      /\ getr regs' 8 = sv 8%nat /\ getr regs' 9 = sv 9%nat /\ getr regs' 18 = sv 18%nat /\ getr regs' 19 = sv 19%nat
      /\ getr regs' 20 = sv 20%nat /\ getr regs' 21 = sv 21%nat /\ getr regs' 22 = sv 22%nat /\ getr regs' 23 = sv 23%nat
      /\ getr regs' 24 = sv 24%nat /\ getr regs' 25 = sv 25%nat
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_RET fx o16_reloc o16_code_ol rom). Qed.

Lemma pd_R0 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x150a4 : word) m rom) (mkst regs' (0x150a8 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 0 /\ regs_agree (fun r => In r [10]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_R0 fx o16_reloc o16_code_ol rom). Qed.

Lemma pd_J94 : forall regs m, exists regs', msteps SEGS (mkst regs (0x14d04 : word) m rom) (mkst regs' (0x150a4 : word) m rom) /\ regs_agree (fun r => False) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_J94 fx o16_reloc o16_code_ol rom). Qed.

Lemma pd_J60 : forall regs m, exists regs', msteps SEGS (mkst regs (0x14fd0 : word) m rom) (mkst regs' (0x150a4 : word) m rom) /\ regs_agree (fun r => False) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_J60 fx o16_reloc o16_code_ol rom). Qed.

Lemma pd_J30 : forall regs m, exists regs', msteps SEGS (mkst regs (0x150a0 : word) m rom) (mkst regs' (0x150a8 : word) m rom) /\ regs_agree (fun r => False) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_J30 fx o16_reloc o16_code_ol rom). Qed.

Lemma pd_G0 : forall regs m (s : Z),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 112)) 112 = true ->
    getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs', msteps SEGS (mkst regs (0x14e98 : word) m rom)
                              (mkst regs' (0x14f74 : word) (wbytes m (Z_to_bv 64 (s - 104)) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ regs_agree (fun r => False) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_G0 fx o16_reloc o16_code_ol rom). Qed.

Lemma pd_G : forall regs m (s dp nb nc pix1 wpl hr ir : Z) (v1 : pixv) bsi,
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 112)) 112 = true ->
    PIXat m pix1 v1 -> (4096 <= pix1)%Z -> (pix1 + 64 <= s - 112)%Z -> p_wpl v1 = wpl -> (1 <= hr <= 1000000)%Z -> (0 <= wpl)%Z -> (4 * (wpl * hr) <= 67108864)%Z ->
    (0 <= nc <= 256)%Z -> (28 <= nb < 2 ^ 31)%Z -> (4 * nc + 32 <= nb)%Z -> (1 <= dp)%Z -> (dp + nb <= s - 112)%Z ->
    rdn SEGS m (Z_to_bv 64 (dp + 4 * nc + 24)) 4 = Some bsi -> bytes_le_to_Z bsi = ir -> (0 <= ir < 2 ^ 32)%Z ->
    getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 10 = Z_to_bv 64 pix1 -> getr regs 23 = Z_to_bv 64 nc -> getr regs 8 = Z_to_bv 64 nb ->
    getr regs 25 = Z_to_bv 64 dp -> getr regs 18 = Z_to_bv 64 hr ->
    exists regs', msteps SEGS (mkst regs (0x14e98 : word) m rom)
                              (mkst regs' (0x13d20 : word) (wbytes m (Z_to_bv 64 (s - 104)) (word_to_le_bytes 8 (Z_to_bv 64 pix1))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 112) /\ getr regs' 10 = Z_to_bv 64 (s - 104) /\ getr regs' 1 = Z_to_bv 64 0x14ed0
      /\ getr regs' 19 = Z_to_bv 64 nc /\ getr regs' 24 = Z_to_bv 64 (dp + 4 * nc) /\ getr regs' 21 = Z_to_bv 64 (zx (sw32 ir))
      /\ getr regs' 8 = Z_to_bv 64 (4 * (wpl * hr)) /\ getr regs' 22 = Z_to_bv 64 (nb - 4 * nc - 28)
      /\ regs_agree (fun r => In r [1; 8; 10; 11; 19; 21; 22; 24]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_G fx o16_reloc o16_code_ol o16_sites_ol rom). Qed.

Lemma pd_H : forall regs m (sz wr hr d : Z),
    (0 <= sz < 2 ^ 32)%Z ->
    getr regs 8 = Z_to_bv 64 sz -> getr regs 22 = Z_to_bv 64 sz -> getr regs 21 = Z_to_bv 64 sz ->
    getr regs 9 = Z_to_bv 64 wr -> getr regs 18 = Z_to_bv 64 hr -> getr regs 20 = Z_to_bv 64 d ->
    exists regs', msteps SEGS (mkst regs (0x14ed0 : word) m rom) (mkst regs' (0x1381c : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 wr /\ getr regs' 11 = Z_to_bv 64 hr /\ getr regs' 12 = Z_to_bv 64 d /\ getr regs' 1 = Z_to_bv 64 0x14ee8
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_H fx o16_reloc o16_code_ol o16_sites_ol rom). Qed.

Lemma pd_Hbad : forall regs m (sz msz isz : Z),
    (0 <= sz < 2 ^ 32)%Z -> (0 <= msz < 2 ^ 32)%Z -> (0 <= isz < 2 ^ 64)%Z -> (sz <> msz \/ sz <> isz) ->
    rdn SEGS m (Z_to_bv 64 0x1e780) 8 = Some (Z_to_le_bytes 8 0x1f7f0) -> rdn SEGS m (Z_to_bv 64 0x1f7f0) 4 = Some (Z_to_le_bytes 4 3) ->
    getr regs 8 = Z_to_bv 64 sz -> getr regs 22 = Z_to_bv 64 msz -> getr regs 21 = Z_to_bv 64 isz ->
    exists regs', msteps SEGS (mkst regs (0x14ed0 : word) m rom) (mkst regs' (0x1371c : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 0x104e0 /\ getr regs' 11 = Z_to_bv 64 0x105cb /\ getr regs' 1 = Z_to_bv 64 0x14fd0
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_Hbad fx o16_reloc o16_code_ol o16_sites_ol rom). Qed.

Lemma pd_I0 : forall regs m (s : Z),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 112)) 112 = true ->
    getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs', msteps SEGS (mkst regs (0x14ee8 : word) m rom)
                              (mkst regs' (0x14fd4 : word) (wbytes m (Z_to_bv 64 (s - 112)) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ regs_agree (fun r => False) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_I0 fx o16_reloc o16_code_ol rom). Qed.

Lemma pd_I1 : forall regs m (s pixd : Z),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 112)) 112 = true -> (1 <= pixd < 2 ^ 64)%Z ->
    getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 10 = Z_to_bv 64 pixd -> getr regs 23 = Z_to_bv 64 0 ->
    exists regs', msteps SEGS (mkst regs (0x14ee8 : word) m rom)
                              (mkst regs' (0x15038 : word) (wbytes m (Z_to_bv 64 (s - 112)) (word_to_le_bytes 8 (Z_to_bv 64 pixd))) rom)
      /\ getr regs' 9 = Z_to_bv 64 0 /\ getr regs' 10 = Z_to_bv 64 pixd /\ regs_agree (fun r => In r [9]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_I1 fx o16_reloc o16_code_ol rom). Qed.

Lemma pd_I2 : forall regs m (s pixd dp nc : Z),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 112)) 112 = true -> (1 <= pixd < 2 ^ 64)%Z -> (1 <= nc <= 256)%Z -> (0 <= dp < 2 ^ 64)%Z ->
    getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 10 = Z_to_bv 64 pixd -> getr regs 23 = Z_to_bv 64 nc -> getr regs 25 = Z_to_bv 64 dp -> getr regs 19 = Z_to_bv 64 nc ->
    exists regs', msteps SEGS (mkst regs (0x14ee8 : word) m rom)
                              (mkst regs' (0x14594 : word) (wbytes m (Z_to_bv 64 (s - 112)) (word_to_le_bytes 8 (Z_to_bv 64 pixd))) rom)
      /\ getr regs' 10 = Z_to_bv 64 (dp + 24) /\ getr regs' 11 = Z_to_bv 64 4 /\ getr regs' 12 = Z_to_bv 64 nc /\ getr regs' 1 = Z_to_bv 64 0x14f04
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_I2 fx o16_reloc o16_code_ol o16_sites_ol rom). Qed.

Lemma pd_J0 : forall regs m (s : Z),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs', msteps SEGS (mkst regs (0x14f04 : word) m rom) (mkst regs' (0x13d20 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 (s - 112) /\ getr regs' 1 = Z_to_bv 64 0x1500c /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_J0 fx o16_reloc o16_code_ol o16_sites_ol rom). Qed.

Lemma pd_J1 : forall regs m (s cm pixd : Z),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= cm < 2 ^ 64)%Z -> (0 <= pixd < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 112)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 pixd)) ->
    getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 10 = Z_to_bv 64 cm ->
    exists regs', msteps SEGS (mkst regs (0x14f04 : word) m rom) (mkst regs' (0x13e6c : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 cm /\ getr regs' 9 = Z_to_bv 64 cm /\ getr regs' 1 = Z_to_bv 64 0x14f18
      /\ regs_agree (fun r => In r [1; 9; 10; 11]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_J1 fx o16_reloc o16_code_ol o16_sites_ol rom). Qed.

Lemma pd_K : forall regs m (s pixd : Z),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= pixd < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 112)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 pixd)) ->
    getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs', msteps SEGS (mkst regs (0x14f18 : word) m rom) (mkst regs' (0x15038 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 pixd /\ regs_agree (fun r => In r [10]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_K fx o16_reloc o16_code_ol rom). Qed.

Lemma pd_GD : forall regs m (pixd e8 sz : Z) (v : pixv),
    PIXat m pixd v -> (4096 <= pixd)%Z -> (0 <= e8)%Z -> (e8 + 28 < 2 ^ 64)%Z ->
    getr regs 10 = Z_to_bv 64 pixd -> getr regs 24 = Z_to_bv 64 e8 -> getr regs 8 = Z_to_bv 64 sz ->
    exists regs', msteps SEGS (mkst regs (0x15038 : word) m rom) (mkst regs' (0x1cd64 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 (p_data v) /\ getr regs' 11 = Z_to_bv 64 (e8 + 28) /\ getr regs' 12 = Z_to_bv 64 sz /\ getr regs' 1 = Z_to_bv 64 0x15048
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_GD fx o16_reloc o16_code_ol o16_sites_ol rom). Qed.

Lemma pd_L0 : forall regs m (s pixd : Z),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= pixd < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 112)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 pixd)) ->
    getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 23 = Z_to_bv 64 0 ->
    exists regs', msteps SEGS (mkst regs (0x15048 : word) m rom) (mkst regs' (0x150a8 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 pixd /\ regs_agree (fun r => In r [10]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_L0 fx o16_reloc o16_code_ol rom). Qed.

Lemma pd_L1 : forall regs m (s pixd nc cm : Z),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= pixd < 2 ^ 64)%Z -> (1 <= nc <= 256)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 112)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 pixd)) ->
    getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 23 = Z_to_bv 64 nc -> getr regs 9 = Z_to_bv 64 cm ->
    exists regs', msteps SEGS (mkst regs (0x15048 : word) m rom) (mkst regs' (0x14214 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 cm /\ getr regs' 11 = Z_to_bv 64 pixd /\ getr regs' 12 = Z_to_bv 64 (s - 92) /\ getr regs' 1 = Z_to_bv 64 0x1505c
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_L1 fx o16_reloc o16_code_ol o16_sites_ol rom). Qed.

Lemma pd_M1 : forall regs m (s pixd : Z),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= pixd < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 92)) 4 = Some (Z_to_le_bytes 4 1) ->
    rdn SEGS m (Z_to_bv 64 (s - 112)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 pixd)) ->
    getr regs 2 = Z_to_bv 64 (s - 112) ->
    exists regs', msteps SEGS (mkst regs (0x1505c : word) m rom) (mkst regs' (0x150a8 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 pixd /\ regs_agree (fun r => In r [10]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_M1 fx o16_reloc o16_code_ol rom). Qed.

Lemma pd_M0 : forall regs m (s : Z),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 92)) 4 = Some (Z_to_le_bytes 4 0) ->
    getr regs 2 = Z_to_bv 64 (s - 112) ->
    exists regs', msteps SEGS (mkst regs (0x1505c : word) m rom) (mkst regs' (0x13d20 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 (s - 112) /\ getr regs' 1 = Z_to_bv 64 0x15074 /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_M0 fx o16_reloc o16_code_ol o16_sites_ol rom). Qed.

End Segs.

End DeserA.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).      (* [comment removed for export] *)
End O16LeptDeserA.

From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.O16 Require O16CL3a.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica.OL Require LeptPadBitsW.
Module O16LeptPadBitsW.
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
Import OSSVerify.leptonica.jpegiostub_fuzzer.images.Plain.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.StepTac.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.AllocIface.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.PureModel.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.VmLedger.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.StoreOk.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.MemSplit.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.RefMemcpyLib.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.StartupTac.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.WalkTac.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Mallocng.AllocBase.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Mallocng.AllocSure.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica.SumWalkTac.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica.SumSpecs.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica.WalksLib.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica.W2Lib.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica.LibAtomic.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica.LeptDefs.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica.LeptStructs.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica.LeptArith.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.O16.O16LeptStderr.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.O16.O16LeptBase.
Import O16CL3a.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica.LeptRoom.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Reloc.Reloc.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica.RelocLept.
Import O16Kit.
Import O16CL7a.
(* [comment removed for export] *)










Import O16CL3a.O16PadBits.





Import O16Kit.O16Reloc. Import O16Kit.O16RelocCode. Import O16Kit.O16RelocSites. Import O16Kit.O16RelocImg. Import O16Kit.O16RelocOL.
Import O16Kit.O16RelocMusl. Import O16Kit.O16LeptEnv.

Import O16CL7a.O16LeptG.
Import ListNotations.
Open Scope bv_scope.

Section PadBitsW.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LL16} {P16 : O16Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
Theorem padbits_W : forall C Ar A m md regs (s pix : Z) (v : pixv) (ret : word) (S : TSet),
  Cok C -> W C A m md -> sub_live Ar A ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 48 + LSF <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 10 = Z_to_bv 64 pix -> getr regs 11 = Z_to_bv 64 0 ->
  PIXat m pix v -> dval (p_d v) -> (1 <= p_w v <= 20000)%Z -> (1 <= p_h v <= 20000)%Z -> p_wpl v = wpl_of (p_w v) (p_d v) ->
  live A (Z_to_bv 64 pix) = Some 64%Z ->
  live A (Z_to_bv 64 (p_data v)) = Some (4 * (p_wpl v * p_h v))%Z -> live Ar (Z_to_bv 64 (p_data v)) = None ->
  live (c_A0 C) (Z_to_bv 64 (p_data v)) = None -> Z_to_bv 64 pix <> Z_to_bv 64 (p_data v) ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C Ar s m m' ->
      PIXat m' pix v -> (getr regs' 10 = Z_to_bv 64 0 \/ getr regs' 10 = Z_to_bv 64 1) ->
      realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (0x14098 : word) m al_rom) md) S.
Proof. rl_tail (@LeptPadBitsW.padbits_W fx o16_reloc o16_code o16_sites o16_code_ol o16_sites_ol o16_lept o16_img_ol o16_data o16_img o16_rw o16_pf o16_lenv_ol AL CL ASR PINS (o16_pinsG P16)). Qed.

End PadBitsW.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).      (* [comment removed for export] *)
End O16LeptPadBitsW.

From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica.OL Require LeptPixHdr.
Module O16LeptPixHdr.
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
Import OSSVerify.leptonica.jpegiostub_fuzzer.images.Plain.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.StepTac.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.AllocIface.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.PureModel.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.VmLedger.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.StoreOk.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.MemSplit.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.RefMemcpyLib.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.StartupTac.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.WalkTac.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Mallocng.AllocBase.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Mallocng.AllocSure.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica.SumWalkTac.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica.SumSpecs.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica.WalksLib.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica.W2Lib.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica.LibAtomic.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica.LeptDefs.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica.LeptStructs.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica.LeptArith.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.O16.O16LeptStderr.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.O16.O16LeptBase.
Import O16CL7a.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica.LeptRoom.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Reloc.Reloc.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica.RelocLept.
Import O16Kit.
(* [comment removed for export] *)










Import O16CL7a.O16LeptErr.





Import O16Kit.O16Reloc. Import O16Kit.O16RelocCode. Import O16Kit.O16RelocSites. Import O16Kit.O16RelocImg. Import O16Kit.O16RelocOL.
Import O16Kit.O16RelocMusl. Import O16Kit.O16LeptEnv.
Import O16CL7a.O16LeptG.
Import ListNotations.
Open Scope bv_scope.

Section PixHdr.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LL16} {P16 : O16Pins}.
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
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x2fb50 ->
  getr regs 10 = Z_to_bv 64 w -> getr regs 11 = Z_to_bv 64 h -> getr regs 12 = Z_to_bv 64 d ->
  (1 <= w <= 1000000)%Z -> (1 <= h <= 1000000)%Z -> (w * h <= 400000000)%Z -> (0 <= d < 2 ^ 64)%Z ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     ((getr regs' 10 = Z_to_bv 64 0 /\ forall q, live A' q = live A q)
      \/ (exists pix, getr regs' 10 = Z_to_bv 64 pix /\ (hdr_ok w h d /\ pix_new C A A' m' pix (pix_hdr w h d)))) ->
     roomtr A (m_vmmaps md) A' vm' RK_hdr RB_hdr ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x139e4 : word) m al_rom) md) S.
Proof. rl_tail (@LeptPixHdr.pixCreateHeader_W fx o16_reloc o16_code o16_sites o16_code_ol o16_sites_ol o16_lept o16_img_ol o16_data o16_img o16_rw o16_pf o16_lenv_ol AL CL ASR PINS (o16_pinsG P16)). Qed.

End PixHdr.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).      (* [comment removed for export] *)
End O16LeptPixHdr.
