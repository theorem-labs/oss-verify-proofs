(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.bilateral_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import StartupTac RefMemcpyLib.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Reloc Require Import Reloc.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import RelocLept.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica.OL Require CmapFill.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.O2 Require Import O2Reloc O2RelocCode O2RelocSites O2RelocImg O2RelocOL.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_O2CmapFill () := "C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00K47Corelib4Init9Datatypes3nat02C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=bytes_le_to_ZK47Corelib7Numbers7BinNums1N02C45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedI47Corelib4Init5Logic2eq00C79OSSVerify5KrLib6Common9Leptonica2OL8CmapFill4lez8C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes3nat01C79OSSVerify5KrLib6Common9Leptonica2OL8CmapFillAcmapfill_contractC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc5Reloc7rl_segsC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C69OSSVerify5KrLib6Common5Reloc5Reloc8rl_deltaC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addI47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C79OSSVerify5KrLib6Common9Leptonica8SumSpecs3SSP=spec_cmapfillC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9Leptonica8SumSpecs3SSP<sum_contractC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O27O2Reloc8o2_relocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O29O2RelocOL:o2_code_olC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00C79OSSVerify5KrLib6Common9Leptonica2OL8CmapFill9CMAP_CLOBC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope bv_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section VPORT.
Context {fx : FPState}.
Definition CMAP_CLOB : list nat := [10; 11; 12; 13; 14; 15; 16; 21; 23]%nat.
Section CF.
Variable M : word -> option byte.
Variable rom : word -> option byte.
Variables cmap dp nc arr nalloc : Z.
Variable bs : list byte.
#[local] Notation data := (dp - 3)%Z (only parsing).
Hypothesis Hcmap : (1 <= cmap /\ cmap + 24 <= 2 ^ 64)%Z.
Hypothesis Hnc : (1 <= nc <= 256)%Z.
Hypothesis Hnal : (nc <= nalloc <= 256)%Z.
Hypothesis Harr : (1 <= arr /\ arr + 4 * nalloc <= 2 ^ 64)%Z.
Hypothesis Hdat : (3 <= dp /\ dp - 3 + 4 * nc <= 2 ^ 64)%Z.
Hypothesis Carr : rdn SEGS M (Z_to_bv 64 cmap) 8 = Some (Z_to_le_bytes 8 arr).
Hypothesis Cnal : rdn SEGS M (Z_to_bv 64 (cmap + 12)) 4 = Some (Z_to_le_bytes 4 nalloc).
Hypothesis Cn0 : rdn SEGS M (Z_to_bv 64 (cmap + 16)) 4 = Some (Z_to_le_bytes 4 0).
Hypothesis Dbs : rdn SEGS M (Z_to_bv 64 (dp - 3)) (Z.to_nat (4 * nc)) = Some bs.
Hypothesis SOKa : store_ok SEGS M (Z_to_bv 64 arr) (Z.to_nat (4 * nalloc)) = true.
Hypothesis SOKc : store_ok SEGS M (Z_to_bv 64 cmap) 24 = true.
Hypothesis A_ca : (cmap + 24 <= arr \/ arr + 4 * nalloc <= cmap)%Z.
Hypothesis A_cd : (cmap + 24 <= dp - 3 \/ dp - 3 + 4 * nc <= cmap)%Z.
Hypothesis A_ad : (arr + 4 * nalloc <= dp - 3 \/ dp - 3 + 4 * nc <= arr)%Z.
Lemma lez8 : forall z, (0 <= z < 2 ^ 64)%Z -> bytes_le_to_Z (Z_to_le_bytes 8 z) = bv_unsigned (Z_to_bv 64 z).
Proof.
ltac2:(KReplay.run1 (kr_t_O2CmapFill ()) ["VPORT"; "CF"] "h03RLTh11zp;2p;1p;3g0000j2<Tg000Lj11Tg0011j12Tg001Oj23Tg001lj2;Tg002Hj2:Tg002cj10Tg003Bj24Tg004?j15Tg005<j16Tg005Zj27Tg006@j28Tg006jj39Tg007Dg008JR0g008hf0R1'<g009F#1R2#2%12#1#1#1#1R2#2'3,;1':g009k#0#0#0#0#0#0#0#0f1R3'4#5%62R21723'8590[]1P1b0o"). Qed.

End CF.

Theorem cmapfill_contract :
  SSP.sum_contract SEGS (SSP.spec_cmapfill 0x1d8b8 0x1d7bc 9 21 3 23 [(8%nat, 4%Z); (20%nat, 4%Z)] CMAP_CLOB).
Proof.
ltac2:(KReplay.run1 (kr_t_O2CmapFill ()) ["VPORT"] "h03RLTp;3p;1p;2p;4p;8g00:Jj3?Tg00;]j1>Tg00<\j10Tg000Lj13Tg0011j15Tg00=Aj2;Tg00>Aj26Tg002cj14Tg00>^j29Tg00?>j47Tg00?^j1:Tg00@>j38Tg00@^j8=Tg00Anj3<Tf0R0#3#3p=2%40#4p=1p,2fxR1g00C=R2g00D53?%>2g009FR3#2R4#0#3#2#0R5#0#3#0#2#0#0#0#2#5%03R3#3#0#2#2,;2R2'6%35#0#0#3#0#3#2#2#5/62g009k#1#1#1#1R2#4R5%45#1#1#1#1#1R5#4R6%53%16g00E1R6g008JR3'9R7P6P3P2%54R4C7P6P3P5P4C7%:758738g00EPG=7<1P0b0o"). Qed.

End VPORT.
