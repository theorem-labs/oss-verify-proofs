(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
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
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.leptonica.grayquant_fuzzer.images Require Plain.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require PropExec.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require CatExec.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require CatSim.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require StepTac.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Hoare.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require StoreOk.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require StartupTac.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require Amb.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require SymExec2.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require SymExec2Sound.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require SymRun.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require SymDrive.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require WalksLib.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require W2Lib.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptStructs.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptExec.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require DitherLib.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require DitherTac.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require DitherLib2.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require DitherTac2.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require DitherTab.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require DitherTab1.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require BandLib.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require LiaFast.
Module O15BandLoop.
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
Import OSSVerify.leptonica.grayquant_fuzzer.images.Plain.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.StepTac.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.StoreOk.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.StartupTac.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.Amb.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymExec2.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymExec2Sound.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymRun.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymDrive.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.WalksLib.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.W2Lib.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptStructs.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptExec.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.DitherLib.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.DitherTac.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.DitherLib2.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.DitherTac2.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.DitherTab.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.DitherTab1.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.BandLib.
(* [comment removed for export] *)







Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.

Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Abbreviation SEGS := Plain.M.loaded_segments.

Lemma wr_readable_img : wr_readable SEGS.
Proof.
  intros seg Hin Hwr. cbn in Hin.
  repeat (destruct Hin as [<-|Hin]; [first [reflexivity | discriminate Hwr] |]). destruct Hin.
Qed.

(* [comment removed for export] *)
Definition ba_hyps (sp datag w h wplg : Z) : Prop :=
  (4096 <= sp <= 140737488355328)%Z /\ (4096 <= datag <= 140737488355328)%Z /\ (datag mod 4 = 0)%Z /\ (1 <= w <= 20000)%Z /\ (1 <= h <= 20000)%Z /\ (1 <= wplg <= 5000)%Z.
Section BA.
Variable rom : word -> option byte.
Variables (sp datag w h wplg : Z).
Hypothesis HYP : ba_hyps sp datag w h wplg.
Ltac dl_facts := pose proof HYP as (R_sp & R_datag & A_datag & R_w & R_h & R_wplg); idtac.
(* [comment removed for export] *)
Lemma ba_1ab7c : forall (fx : FPState) regs m ,
  rdn SEGS m (Z_to_bv 64 (sp + 16)) 4 = Some (Z_to_le_bytes 4 h) ->
  rdn SEGS m (Z_to_bv 64 (sp + 20)) 4 = Some (Z_to_le_bytes 4 w) ->
  getr regs 2 = Z_to_bv 64 sp ->
  getr regs 18 = Z_to_bv 64 datag ->
  getr regs 19 = Z_to_bv 64 wplg ->
  getr regs 22 = Z_to_bv 64 1 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1ac78) m rom) (@mkst fx regs' (Z_to_bv 64 0x1acb4) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 5 = Z_to_bv 64 h
    /\ getr regs' 11 = Z_to_bv 64 0
    /\ getr regs' 12 = Z_to_bv 64 (4 * wplg)
    /\ getr regs' 13 = Z_to_bv 64 4
    /\ getr regs' 14 = Z_to_bv 64 0
    /\ getr regs' 15 = Z_to_bv 64 18446744071562067968
    /\ getr regs' 16 = Z_to_bv 64 8
    /\ getr regs' 17 = Z_to_bv 64 datag
    /\ getr regs' 31 = Z_to_bv 64 w
    /\ regs_agree (fun r => In r [5; 11; 12; 13; 14; 15; 16; 17; 31]%list) regs regs'.
Proof using All.
  intros fx regs m  KC0 KC1 H2 H18 H19 H22.
  dl_facts.
  ex_entry regs [sp; datag; w; h; wplg] HR.
  assert (HK : know_ok SEGS (ex_env regs [sp; datag; w; h; wplg]) m [KWord (SA (EVar 32) (16)) 4 (EVar 35); KWord (SA (EVar 32) (20)) 4 (EVar 34); KRange (EVar 32) 4096 140737488355328; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 1 20000; KRange (EVar 35) 1 20000; KRange (EVar 36) 1 5000]) by (ex_know regs).
  dl_run 400%nat [109748%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

End BA.

(* [comment removed for export] *)
Definition br_hyps (sp datag datad w i wplg wpld : Z) : Prop :=
  (4096 <= sp <= 140737488355328)%Z /\ (4096 <= datag <= 140737488355328)%Z /\ (datag mod 4 = 0)%Z /\ (4096 <= datad <= 140737488355328)%Z /\ (datad mod 4 = 0)%Z /\ (1 <= w <= 20000)%Z /\ (0 <= i <= 19999)%Z /\ (1 <= wplg <= 5000)%Z /\ (1 <= wpld <= 5000)%Z /\ (0 <= i * wplg < 2 ^ 24)%Z /\ (0 <= i * wpld < 2 ^ 24)%Z.
Section BR.
Variable rom : word -> option byte.
Variables (sp datag datad w i wplg wpld : Z).
Hypothesis HYP : br_hyps sp datag datad w i wplg wpld.
Ltac dl_facts := pose proof HYP as (R_sp & R_datag & A_datag & R_datad & A_datad & R_w & R_i & R_wplg & R_wpld & Hpg & Hpd); idtac.
(* [comment removed for export] *)
Lemma br_1abb8 : forall (fx : FPState) regs m ,
  getr regs 2 = Z_to_bv 64 sp ->
  getr regs 10 = Z_to_bv 64 wpld ->
  getr regs 11 = Z_to_bv 64 i ->
  getr regs 18 = Z_to_bv 64 datag ->
  getr regs 19 = Z_to_bv 64 wplg ->
  getr regs 20 = Z_to_bv 64 datad ->
  getr regs 31 = Z_to_bv 64 w ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1acb4) m rom) (@mkst fx regs' (Z_to_bv 64 0x1acfc) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 5 = Z_to_bv 64 0
    /\ getr regs' 6 = Z_to_bv 64 0
    /\ getr regs' 7 = Z_to_bv 64 0
    /\ getr regs' 28 = Z_to_bv 64 0
    /\ getr regs' 29 = Z_to_bv 64 (datag + (4 * (i * wplg)))
    /\ getr regs' 30 = Z_to_bv 64 (datad + (4 * (i * wpld)))
    /\ regs_agree (fun r => In r [5; 6; 7; 28; 29; 30]%list) regs regs'.
Proof using All.
  intros fx regs m  H2 H10 H11 H18 H19 H20 H31.
  dl_facts.
  ex_entry regs [sp; datag; datad; w; i; wplg; wpld] HR.
  assert (HK : know_ok SEGS (ex_env regs [sp; datag; datad; w; i; wplg; wpld]) m [KRange (EVar 32) 4096 140737488355328; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 1 20000; KRange (EVar 36) 0 19999; KRange (EVar 37) 1 5000; KRange (EVar 38) 1 5000]) by (ex_know regs).
  dl_run 400%nat [109820%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

End BR.

(* [comment removed for export] *)
Definition bl_hyps (sp lineg h i g4 : Z) : Prop :=
  (4096 <= sp <= 140737488355328)%Z /\ (4096 <= lineg <= 140737488355328)%Z /\ (lineg mod 4 = 0)%Z /\ (1 <= h <= 20000)%Z /\ (0 <= i <= 19999)%Z /\ (4 <= g4 <= 20000)%Z /\ (g4 mod 4 = 0)%Z /\ (0 <= i < h)%Z.
Section BL.
Variable rom : word -> option byte.
Variables (sp lineg h i g4 : Z).
Hypothesis HYP : bl_hyps sp lineg h i g4.
Ltac dl_facts := pose proof HYP as (R_sp & R_lineg & A_lineg & R_h & R_i & R_g4 & A_g4 & Hi); idtac.
(* [comment removed for export] *)
Lemma bl_1aba8 : forall (fx : FPState) regs m ,
  rdn SEGS m (Z_to_bv 64 (sp + 16)) 4 = Some (Z_to_le_bytes 4 h) ->
  getr regs 2 = Z_to_bv 64 sp ->
  getr regs 11 = Z_to_bv 64 i ->
  getr regs 12 = Z_to_bv 64 g4 ->
  getr regs 17 = Z_to_bv 64 lineg ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1aca4) m rom) (@mkst fx regs' (Z_to_bv 64 0x1acb0) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 5 = Z_to_bv 64 h
    /\ getr regs' 11 = Z_to_bv 64 (i + 1)
    /\ getr regs' 17 = Z_to_bv 64 (lineg + g4)
    /\ regs_agree (fun r => In r [5; 11; 17]%list) regs regs'.
Proof using All.
  intros fx regs m  KC0 H2 H11 H12 H17.
  dl_facts.
  ex_entry regs [sp; lineg; h; i; g4; (lineg + g4)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [sp; lineg; h; i; g4; (lineg + g4)%Z]) m [KWord (SA (EVar 32) (16)) 4 (EVar 34); KRange (EVar 32) 4096 140737488355328; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 1 20000; KRange (EVar 35) 0 19999; KRange (EVar 36) 4 20000; KAlign (EVar 36) 4; KRange (EVar 37) 4100 140737488375328]) by (ex_know regs).
  dl_run 400%nat [109748%Z; 109964%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma bl_1abb4f : forall (fx : FPState) regs m ,
  branch_taken BC_GE (Z_to_bv 64 (i + 1)) (Z_to_bv 64 h) = false ->
  rdn SEGS m (Z_to_bv 64 (sp + 16)) 4 = Some (Z_to_le_bytes 4 h) ->
  getr regs 2 = Z_to_bv 64 sp ->
  getr regs 5 = Z_to_bv 64 h ->
  getr regs 11 = Z_to_bv 64 (i + 1) ->
  getr regs 12 = Z_to_bv 64 g4 ->
  getr regs 17 = Z_to_bv 64 (lineg + g4) ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1acb0) m rom) (@mkst fx regs' (Z_to_bv 64 0x1acb4) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r []%list) regs regs'.
Proof using All.
  intros fx regs m  BT KC0 H2 H5 H11 H12 H17.
  dl_facts.
  ex_entry regs [sp; lineg; h; i; g4; (lineg + g4)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [sp; lineg; h; i; g4; (lineg + g4)%Z]) m [KWord (SA (EVar 32) (16)) 4 (EVar 34); KRange (EVar 32) 4096 140737488355328; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 1 20000; KRange (EVar 35) 0 19999; KRange (EVar 36) 4 20000; KAlign (EVar 36) 4; KRange (EVar 37) 4100 140737488375328]) by (ex_know regs).
  dl_run 400%nat [109748%Z; 109964%Z] (SCR [false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma bl_1abb4t : forall (fx : FPState) regs m ,
  branch_taken BC_GE (Z_to_bv 64 (i + 1)) (Z_to_bv 64 h) = true ->
  rdn SEGS m (Z_to_bv 64 (sp + 16)) 4 = Some (Z_to_le_bytes 4 h) ->
  getr regs 2 = Z_to_bv 64 sp ->
  getr regs 5 = Z_to_bv 64 h ->
  getr regs 11 = Z_to_bv 64 (i + 1) ->
  getr regs 12 = Z_to_bv 64 g4 ->
  getr regs 17 = Z_to_bv 64 (lineg + g4) ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1acb0) m rom) (@mkst fx regs' (Z_to_bv 64 0x1ad8c) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r []%list) regs regs'.
Proof using All.
  intros fx regs m  BT KC0 H2 H5 H11 H12 H17.
  dl_facts.
  ex_entry regs [sp; lineg; h; i; g4; (lineg + g4)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [sp; lineg; h; i; g4; (lineg + g4)%Z]) m [KWord (SA (EVar 32) (16)) 4 (EVar 34); KRange (EVar 32) 4096 140737488355328; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 1 20000; KRange (EVar 35) 0 19999; KRange (EVar 36) 4 20000; KAlign (EVar 36) 4; KRange (EVar 37) 4100 140737488375328]) by (ex_know regs).
  dl_run 400%nat [109748%Z; 109964%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

End BL.
End O15BandLoop.

Module O15BandPix2.
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
Import OSSVerify.leptonica.grayquant_fuzzer.images.Plain.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.StepTac.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.StoreOk.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.StartupTac.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.Amb.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymExec2.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymExec2Sound.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymRun.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymDrive.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.WalksLib.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.W2Lib.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptStructs.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptExec.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.DitherLib.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.DitherTac.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.DitherLib2.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.DitherTac2.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.DitherTab.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.DitherTab1.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.BandLib.
(* [comment removed for export] *)







Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.

Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Abbreviation SEGS := Plain.M.loaded_segments.

Lemma wr_readable_img : wr_readable SEGS.
Proof.
  intros seg Hin Hwr. cbn in Hin.
  repeat (destruct Hin as [<-|Hin]; [first [reflexivity | discriminate Hwr] |]). destruct Hin.
Qed.

Definition bp2_1ac00_cells_def (sp lineg lined w j wplg wpld : Z) : list (Z * Z) := [((lineg + (4 * (j / 16)))%Z, 4%Z); ((lined + (4 * (j / 32)))%Z, 4%Z)].
Definition bp2_1ac00_cells_w_def (sp lineg lined w j wplg wpld : Z) : list (Z * Z) := [((lined + (4 * (j / 32)))%Z, 4%Z)].
(* [comment removed for export] *)
Definition bp2_hyps (sp lineg lined w j wplg wpld : Z) : Prop :=
  (4096 <= sp <= 140737488355328)%Z /\ (4096 <= lineg <= 140737488355328)%Z /\ (lineg mod 4 = 0)%Z /\ (4096 <= lined <= 140737488355328)%Z /\ (lined mod 4 = 0)%Z /\ (1 <= w <= 20000)%Z /\ (0 <= j <= 19999)%Z /\ (0 <= j < w)%Z /\ (w * 2 <= 32 * wplg)%Z /\ (w <= 32 * wpld)%Z /\ dapart lined (4 * wpld) sp 96.
Section BP2.
Variable rom : word -> option byte.
Variables (sp lineg lined w j wplg wpld : Z).
Hypothesis HYP : bp2_hyps sp lineg lined w j wplg wpld.
Ltac dl_facts := pose proof HYP as (R_sp & R_lineg & A_lineg & R_lined & A_lined & R_w & R_j & Hj & Hwg & Hwd & AP_df); pose proof (dl_div_bounds j 32 ltac:(lia) ltac:(lia)) as DJ; pose proof (dl_div_bounds j 16 ltac:(lia) ltac:(lia)) as DJ16; pose proof (dl_div_bounds j 8 ltac:(lia) ltac:(lia)) as DJ8; destruct (al4_ex _ A_lined) as [cd Ecd]; destruct (al4_ex _ A_lineg) as [cs Ecs].
(* [comment removed for export] *)
Lemma bp2_1abe8 : forall (fx : FPState) regs m ,
  rdn SEGS m (Z_to_bv 64 (sp + 12)) 4 = Some (Z_to_le_bytes 4 2) ->
  rdn SEGS m (Z_to_bv 64 (sp + 20)) 4 = Some (Z_to_le_bytes 4 w) ->
  getr regs 2 = Z_to_bv 64 sp ->
  getr regs 28 = Z_to_bv 64 j ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1ace4) m rom) (@mkst fx regs' (Z_to_bv 64 0x1acf8) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 28 = Z_to_bv 64 (j + 1)
    /\ getr regs' 31 = Z_to_bv 64 w
    /\ regs_agree (fun r => In r [5; 6; 7; 28; 31]%list) regs regs'.
Proof using All.
  intros fx regs m  KC0 KC1 H2 H28.
  dl_facts.
  ex_entry regs [sp; lineg; lined; w; j] HR.
  assert (HK : know_ok SEGS (ex_env regs [sp; lineg; lined; w; j]) m [KWord (SA (EVar 32) (12)) 4 (ELit 2); KWord (SA (EVar 32) (20)) 4 (EVar 35); KRange (EVar 32) 4096 140737488355328; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 1 20000; KRange (EVar 36) 0 19999]) by (ex_know regs).
  dl_run 400%nat [109732%Z; 109796%Z; 109820%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma bp2_1abfcf : forall (fx : FPState) regs m ,
  branch_taken BC_GE (Z_to_bv 64 (j + 1)) (Z_to_bv 64 w) = false ->
  rdn SEGS m (Z_to_bv 64 (sp + 12)) 4 = Some (Z_to_le_bytes 4 2) ->
  rdn SEGS m (Z_to_bv 64 (sp + 20)) 4 = Some (Z_to_le_bytes 4 w) ->
  getr regs 2 = Z_to_bv 64 sp ->
  getr regs 28 = Z_to_bv 64 (j + 1) ->
  getr regs 31 = Z_to_bv 64 w ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1acf8) m rom) (@mkst fx regs' (Z_to_bv 64 0x1acfc) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r []%list) regs regs'.
Proof using All.
  intros fx regs m  BT KC0 KC1 H2 H28 H31.
  dl_facts.
  ex_entry regs [sp; lineg; lined; w; j] HR.
  assert (HK : know_ok SEGS (ex_env regs [sp; lineg; lined; w; j]) m [KWord (SA (EVar 32) (12)) 4 (ELit 2); KWord (SA (EVar 32) (20)) 4 (EVar 35); KRange (EVar 32) 4096 140737488355328; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 1 20000; KRange (EVar 36) 0 19999]) by (ex_know regs).
  dl_run 400%nat [109732%Z; 109796%Z; 109820%Z] (SCR [false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma bp2_1abfct : forall (fx : FPState) regs m ,
  branch_taken BC_GE (Z_to_bv 64 (j + 1)) (Z_to_bv 64 w) = true ->
  rdn SEGS m (Z_to_bv 64 (sp + 12)) 4 = Some (Z_to_le_bytes 4 2) ->
  rdn SEGS m (Z_to_bv 64 (sp + 20)) 4 = Some (Z_to_le_bytes 4 w) ->
  getr regs 2 = Z_to_bv 64 sp ->
  getr regs 28 = Z_to_bv 64 (j + 1) ->
  getr regs 31 = Z_to_bv 64 w ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1acf8) m rom) (@mkst fx regs' (Z_to_bv 64 0x1aca4) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r []%list) regs regs'.
Proof using All.
  intros fx regs m  BT KC0 KC1 H2 H28 H31.
  dl_facts.
  ex_entry regs [sp; lineg; lined; w; j] HR.
  assert (HK : know_ok SEGS (ex_env regs [sp; lineg; lined; w; j]) m [KWord (SA (EVar 32) (12)) 4 (ELit 2); KWord (SA (EVar 32) (20)) 4 (EVar 35); KRange (EVar 32) 4096 140737488355328; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 1 20000; KRange (EVar 36) 0 19999]) by (ex_know regs).
  dl_run 400%nat [109732%Z; 109796%Z; 109820%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma bp2_1ac00 : forall (fx : FPState) regs m (bs0 : list byte),
  rdn SEGS m (Z_to_bv 64 (lineg + (4 * (j / 16)))) 4 = Some bs0 ->
  rdn SEGS m (Z_to_bv 64 (sp + 12)) 4 = Some (Z_to_le_bytes 4 2) ->
  rdn SEGS m (Z_to_bv 64 (sp + 20)) 4 = Some (Z_to_le_bytes 4 w) ->
  getr regs 2 = Z_to_bv 64 sp ->
  getr regs 8 = Z_to_bv 64 2 ->
  getr regs 9 = Z_to_bv 64 1 ->
  getr regs 13 = Z_to_bv 64 4 ->
  getr regs 14 = Z_to_bv 64 0 ->
  getr regs 16 = Z_to_bv 64 8 ->
  getr regs 17 = Z_to_bv 64 lineg ->
  getr regs 28 = Z_to_bv 64 j ->
  getr regs 29 = Z_to_bv 64 lineg ->
  getr regs 30 = Z_to_bv 64 lined ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1acfc) m rom) (@mkst fx regs' (Z_to_bv 64 0x1ad68) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r [21; 31]%list) regs regs'.
Proof using All.
  intros fx regs m bs0 R0 KC0 KC1 H2 H8 H9 H13 H14 H16 H17 H28 H29 H30.
  dl_facts.
  ex_entry regs [sp; lineg; lined; w; j; rdv true 4 bs0] HR.
  assert (HK : know_ok SEGS (ex_env regs [sp; lineg; lined; w; j; rdv true 4 bs0]) m [KWord (SA (EVar 32) (12)) 4 (ELit 2); KWord (SA (EVar 32) (20)) 4 (EVar 35); KRange (EVar 32) 4096 140737488355328; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 1 20000; KRange (EVar 36) 0 19999]) by (ex_know regs).
  dl_run 400%nat [109732%Z; 109796%Z; 109820%Z] (SCR [] [EVar 37] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma bp2_1ac6cf : forall (fx : FPState) regs m (bs0 : list byte),
  branch_taken BC_NE (Z_to_bv 64 0) (getr regs 31) = false ->
  rdn SEGS m (Z_to_bv 64 (lined + (4 * (j / 32)))) 4 = Some bs0 ->
  store_ok SEGS m (Z_to_bv 64 (lined + (4 * (j / 32)))) 4 = true ->
  rdn SEGS m (Z_to_bv 64 (sp + 12)) 4 = Some (Z_to_le_bytes 4 2) ->
  rdn SEGS m (Z_to_bv 64 (sp + 20)) 4 = Some (Z_to_le_bytes 4 w) ->
  getr regs 2 = Z_to_bv 64 sp ->
  getr regs 8 = Z_to_bv 64 2 ->
  getr regs 9 = Z_to_bv 64 1 ->
  getr regs 13 = Z_to_bv 64 4 ->
  getr regs 14 = Z_to_bv 64 0 ->
  getr regs 16 = Z_to_bv 64 8 ->
  getr regs 17 = Z_to_bv 64 lineg ->
  getr regs 28 = Z_to_bv 64 j ->
  getr regs 29 = Z_to_bv 64 lineg ->
  getr regs 30 = Z_to_bv 64 lined ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1ad68) m rom) (@mkst fx regs' (Z_to_bv 64 0x1ace4) m' rom)
    /\ mframe [((lined + (4 * (j / 32)))%Z, 4%Z)] m m'
    /\ getr regs' 31 = Z_to_bv 64 (lined + (4 * (j / 32)))
    /\ regs_agree (fun r => In r [21; 22; 31]%list) regs regs'.
Proof using All.
  intros fx regs m bs0 BT R0 S0 KC0 KC1 H2 H8 H9 H13 H14 H16 H17 H28 H29 H30.
  dl_facts.
  ex_entry regs [sp; lineg; lined; w; j; rdv true 4 bs0] HR.
  assert (HK : know_ok SEGS (ex_env regs [sp; lineg; lined; w; j; rdv true 4 bs0]) m [KWord (SA (EVar 32) (12)) 4 (ELit 2); KWord (SA (EVar 32) (20)) 4 (EVar 35); KRange (EVar 32) 4096 140737488355328; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 1 20000; KRange (EVar 36) 0 19999]) by (ex_know regs).
  dl_run 400%nat [109732%Z; 109796%Z; 109820%Z] (SCR [false] [EVar 37] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma bp2_1ac6ct : forall (fx : FPState) regs m ,
  branch_taken BC_NE (Z_to_bv 64 0) (getr regs 31) = true ->
  rdn SEGS m (Z_to_bv 64 (sp + 12)) 4 = Some (Z_to_le_bytes 4 2) ->
  rdn SEGS m (Z_to_bv 64 (sp + 20)) 4 = Some (Z_to_le_bytes 4 w) ->
  getr regs 2 = Z_to_bv 64 sp ->
  getr regs 8 = Z_to_bv 64 2 ->
  getr regs 9 = Z_to_bv 64 1 ->
  getr regs 13 = Z_to_bv 64 4 ->
  getr regs 14 = Z_to_bv 64 0 ->
  getr regs 16 = Z_to_bv 64 8 ->
  getr regs 17 = Z_to_bv 64 lineg ->
  getr regs 28 = Z_to_bv 64 j ->
  getr regs 29 = Z_to_bv 64 lineg ->
  getr regs 30 = Z_to_bv 64 lined ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1ad68) m rom) (@mkst fx regs' (Z_to_bv 64 0x1ace4) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r []%list) regs regs'.
Proof using All.
  intros fx regs m  BT KC0 KC1 H2 H8 H9 H13 H14 H16 H17 H28 H29 H30.
  dl_facts.
  ex_entry regs [sp; lineg; lined; w; j] HR.
  assert (HK : know_ok SEGS (ex_env regs [sp; lineg; lined; w; j]) m [KWord (SA (EVar 32) (12)) 4 (ELit 2); KWord (SA (EVar 32) (20)) 4 (EVar 35); KRange (EVar 32) 4096 140737488355328; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 1 20000; KRange (EVar 36) 0 19999]) by (ex_know regs).
  dl_run 400%nat [109732%Z; 109796%Z; 109820%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Local Abbreviation bp2_1ac00_cells := (bp2_1ac00_cells_def sp lineg lined w j wplg wpld).
Local Abbreviation bp2_1ac00_cells_w := (bp2_1ac00_cells_w_def sp lineg lined w j wplg wpld).
Lemma bp2_1ac00_path : forall (fx : FPState) regs m,
  cells_ok SEGS m bp2_1ac00_cells ->
  (forall m', mframe bp2_1ac00_cells_w m m' -> rdn SEGS m' (Z_to_bv 64 (sp + 12)) 4 = Some (Z_to_le_bytes 4 2)) ->
  (forall m', mframe bp2_1ac00_cells_w m m' -> rdn SEGS m' (Z_to_bv 64 (sp + 20)) 4 = Some (Z_to_le_bytes 4 w)) ->
  getr regs 2 = Z_to_bv 64 sp ->
  getr regs 8 = Z_to_bv 64 2 ->
  getr regs 9 = Z_to_bv 64 1 ->
  getr regs 13 = Z_to_bv 64 4 ->
  getr regs 14 = Z_to_bv 64 0 ->
  getr regs 16 = Z_to_bv 64 8 ->
  getr regs 17 = Z_to_bv 64 lineg ->
  getr regs 28 = Z_to_bv 64 j ->
  getr regs 29 = Z_to_bv 64 lineg ->
  getr regs 30 = Z_to_bv 64 lined ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1acfc) m rom) (@mkst fx regs' (Z_to_bv 64 0x1ace4) m' rom)
    /\ mframe bp2_1ac00_cells m m'
    /\ mframe bp2_1ac00_cells_w m m'
    /\ regs_agree (fun r => In r [21; 22; 31]%list) regs regs'.
Proof using All.
  intros fx regs m CK  KCM0 KCM1 H2 H8 H9 H13 H14 H16 H17 H28 H29 H30.
  pose proof (mframe_refl bp2_1ac00_cells m) as FK0.
  pose proof (mframe_refl bp2_1ac00_cells_w m) as FW0.
  destruct (cells_ok_read SEGS m m bp2_1ac00_cells (lineg + (4 * (j / 16)))%Z 4%Z wr_readable_img CK (proj1 FK0) ltac:(dl_in0)) as [bs1_0 Rd1_0].
  destruct (bp2_1ac00 fx regs m bs1_0 Rd1_0 (KCM0 m FW0) (KCM1 m FW0) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r1 & m1 & RUN1 & FR1 & AG1).
  assert (FK1 : mframe bp2_1ac00_cells m m1) by (apply (mframe_step _ _ _ _ _ FK0 FR1); unfold bp2_1ac00_cells_def; dl_incl).
  assert (FW1 : mframe bp2_1ac00_cells_w m m1) by (apply (mframe_step _ _ _ _ _ FW0 FR1); unfold bp2_1ac00_cells_w_def; dl_incl).
  destruct (branch_taken BC_NE (Z_to_bv 64 0) (getr r1 31)) eqn:B1.
  - (* [comment removed for export] *)
    destruct (bp2_1ac6ct fx r1 m1  B1 (KCM0 m1 FW1) (KCM1 m1 FW1) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r2 & m2 & RUN2 & FR2 & AG2).
    assert (FK2 : mframe bp2_1ac00_cells m m2) by (apply (mframe_step _ _ _ _ _ FK1 FR2); unfold bp2_1ac00_cells_def; dl_incl).
    assert (FW2 : mframe bp2_1ac00_cells_w m m2) by (apply (mframe_step _ _ _ _ _ FW1 FR2); unfold bp2_1ac00_cells_w_def; dl_incl).
    exists r2, m2. split; [exact (msteps_trans _ _ _ _ RUN1 RUN2)|]. split; [exact FK2|]. split; [exact FW2|].
    repeat split; [dl_get .. | ra_chain].
  - (* [comment removed for export] *)
    destruct (cells_ok_read SEGS m m1 bp2_1ac00_cells (lined + (4 * (j / 32)))%Z 4%Z wr_readable_img CK (proj1 FK1) ltac:(dl_in0)) as [bs2_0 Rd2_0].
    destruct (bp2_1ac6cf fx r1 m1 bs2_0 B1 Rd2_0 (cells_ok_sok SEGS m m1 bp2_1ac00_cells (lined + (4 * (j / 32)))%Z 4%Z CK (proj1 FK1) ltac:(dl_in0)) (KCM0 m1 FW1) (KCM1 m1 FW1) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r2 & m2 & RUN2 & FR2 & E2_31 & AG2).
    assert (FK2 : mframe bp2_1ac00_cells m m2) by (apply (mframe_step _ _ _ _ _ FK1 FR2); unfold bp2_1ac00_cells_def; dl_incl).
    assert (FW2 : mframe bp2_1ac00_cells_w m m2) by (apply (mframe_step _ _ _ _ _ FW1 FR2); unfold bp2_1ac00_cells_w_def; dl_incl).
    exists r2, m2. split; [exact (msteps_trans _ _ _ _ RUN1 RUN2)|]. split; [exact FK2|]. split; [exact FW2|].
    repeat split; [dl_get .. | ra_chain].
Qed.

End BP2.
End O15BandPix2.

Module O15BandPix4.
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
Import OSSVerify.leptonica.grayquant_fuzzer.images.Plain.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.StepTac.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.StoreOk.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.StartupTac.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.Amb.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymExec2.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymExec2Sound.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymRun.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymDrive.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.WalksLib.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.W2Lib.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptStructs.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptExec.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.DitherLib.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.DitherTac.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.DitherLib2.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.DitherTac2.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.DitherTab.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.DitherTab1.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.BandLib.
(* [comment removed for export] *)







Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.

Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Abbreviation SEGS := Plain.M.loaded_segments.

Lemma wr_readable_img : wr_readable SEGS.
Proof.
  intros seg Hin Hwr. cbn in Hin.
  repeat (destruct Hin as [<-|Hin]; [first [reflexivity | discriminate Hwr] |]). destruct Hin.
Qed.

Definition bp4_1ac00_cells_def (sp lineg lined w j wplg wpld : Z) : list (Z * Z) := [((lineg + (4 * (j / 8)))%Z, 4%Z); ((lined + (4 * (j / 32)))%Z, 4%Z)].
Definition bp4_1ac00_cells_w_def (sp lineg lined w j wplg wpld : Z) : list (Z * Z) := [((lined + (4 * (j / 32)))%Z, 4%Z)].
(* [comment removed for export] *)
Definition bp4_hyps (sp lineg lined w j wplg wpld : Z) : Prop :=
  (4096 <= sp <= 140737488355328)%Z /\ (4096 <= lineg <= 140737488355328)%Z /\ (lineg mod 4 = 0)%Z /\ (4096 <= lined <= 140737488355328)%Z /\ (lined mod 4 = 0)%Z /\ (1 <= w <= 20000)%Z /\ (0 <= j <= 19999)%Z /\ (0 <= j < w)%Z /\ (w * 4 <= 32 * wplg)%Z /\ (w <= 32 * wpld)%Z /\ dapart lined (4 * wpld) sp 96.
Section BP4.
Variable rom : word -> option byte.
Variables (sp lineg lined w j wplg wpld : Z).
Hypothesis HYP : bp4_hyps sp lineg lined w j wplg wpld.
Ltac dl_facts := pose proof HYP as (R_sp & R_lineg & A_lineg & R_lined & A_lined & R_w & R_j & Hj & Hwg & Hwd & AP_df); pose proof (dl_div_bounds j 32 ltac:(lia) ltac:(lia)) as DJ; pose proof (dl_div_bounds j 16 ltac:(lia) ltac:(lia)) as DJ16; pose proof (dl_div_bounds j 8 ltac:(lia) ltac:(lia)) as DJ8; destruct (al4_ex _ A_lined) as [cd Ecd]; destruct (al4_ex _ A_lineg) as [cs Ecs].
(* [comment removed for export] *)
Lemma bp4_1abe8 : forall (fx : FPState) regs m ,
  rdn SEGS m (Z_to_bv 64 (sp + 12)) 4 = Some (Z_to_le_bytes 4 4) ->
  rdn SEGS m (Z_to_bv 64 (sp + 20)) 4 = Some (Z_to_le_bytes 4 w) ->
  getr regs 2 = Z_to_bv 64 sp ->
  getr regs 28 = Z_to_bv 64 j ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1ace4) m rom) (@mkst fx regs' (Z_to_bv 64 0x1acf8) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 28 = Z_to_bv 64 (j + 1)
    /\ getr regs' 31 = Z_to_bv 64 w
    /\ regs_agree (fun r => In r [5; 6; 7; 28; 31]%list) regs regs'.
Proof using All.
  intros fx regs m  KC0 KC1 H2 H28.
  dl_facts.
  ex_entry regs [sp; lineg; lined; w; j] HR.
  assert (HK : know_ok SEGS (ex_env regs [sp; lineg; lined; w; j]) m [KWord (SA (EVar 32) (12)) 4 (ELit 4); KWord (SA (EVar 32) (20)) 4 (EVar 35); KRange (EVar 32) 4096 140737488355328; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 1 20000; KRange (EVar 36) 0 19999]) by (ex_know regs).
  dl_run 400%nat [109732%Z; 109796%Z; 109820%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma bp4_1abfcf : forall (fx : FPState) regs m ,
  branch_taken BC_GE (Z_to_bv 64 (j + 1)) (Z_to_bv 64 w) = false ->
  rdn SEGS m (Z_to_bv 64 (sp + 12)) 4 = Some (Z_to_le_bytes 4 4) ->
  rdn SEGS m (Z_to_bv 64 (sp + 20)) 4 = Some (Z_to_le_bytes 4 w) ->
  getr regs 2 = Z_to_bv 64 sp ->
  getr regs 28 = Z_to_bv 64 (j + 1) ->
  getr regs 31 = Z_to_bv 64 w ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1acf8) m rom) (@mkst fx regs' (Z_to_bv 64 0x1acfc) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r []%list) regs regs'.
Proof using All.
  intros fx regs m  BT KC0 KC1 H2 H28 H31.
  dl_facts.
  ex_entry regs [sp; lineg; lined; w; j] HR.
  assert (HK : know_ok SEGS (ex_env regs [sp; lineg; lined; w; j]) m [KWord (SA (EVar 32) (12)) 4 (ELit 4); KWord (SA (EVar 32) (20)) 4 (EVar 35); KRange (EVar 32) 4096 140737488355328; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 1 20000; KRange (EVar 36) 0 19999]) by (ex_know regs).
  dl_run 400%nat [109732%Z; 109796%Z; 109820%Z] (SCR [false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma bp4_1abfct : forall (fx : FPState) regs m ,
  branch_taken BC_GE (Z_to_bv 64 (j + 1)) (Z_to_bv 64 w) = true ->
  rdn SEGS m (Z_to_bv 64 (sp + 12)) 4 = Some (Z_to_le_bytes 4 4) ->
  rdn SEGS m (Z_to_bv 64 (sp + 20)) 4 = Some (Z_to_le_bytes 4 w) ->
  getr regs 2 = Z_to_bv 64 sp ->
  getr regs 28 = Z_to_bv 64 (j + 1) ->
  getr regs 31 = Z_to_bv 64 w ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1acf8) m rom) (@mkst fx regs' (Z_to_bv 64 0x1aca4) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r []%list) regs regs'.
Proof using All.
  intros fx regs m  BT KC0 KC1 H2 H28 H31.
  dl_facts.
  ex_entry regs [sp; lineg; lined; w; j] HR.
  assert (HK : know_ok SEGS (ex_env regs [sp; lineg; lined; w; j]) m [KWord (SA (EVar 32) (12)) 4 (ELit 4); KWord (SA (EVar 32) (20)) 4 (EVar 35); KRange (EVar 32) 4096 140737488355328; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 1 20000; KRange (EVar 36) 0 19999]) by (ex_know regs).
  dl_run 400%nat [109732%Z; 109796%Z; 109820%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma bp4_1ac00 : forall (fx : FPState) regs m (bs0 : list byte),
  rdn SEGS m (Z_to_bv 64 (lineg + (4 * (j / 8)))) 4 = Some bs0 ->
  rdn SEGS m (Z_to_bv 64 (sp + 12)) 4 = Some (Z_to_le_bytes 4 4) ->
  rdn SEGS m (Z_to_bv 64 (sp + 20)) 4 = Some (Z_to_le_bytes 4 w) ->
  getr regs 2 = Z_to_bv 64 sp ->
  getr regs 8 = Z_to_bv 64 2 ->
  getr regs 9 = Z_to_bv 64 1 ->
  getr regs 13 = Z_to_bv 64 4 ->
  getr regs 14 = Z_to_bv 64 0 ->
  getr regs 16 = Z_to_bv 64 8 ->
  getr regs 17 = Z_to_bv 64 lineg ->
  getr regs 28 = Z_to_bv 64 j ->
  getr regs 29 = Z_to_bv 64 lineg ->
  getr regs 30 = Z_to_bv 64 lined ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1acfc) m rom) (@mkst fx regs' (Z_to_bv 64 0x1ad68) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r [21; 31]%list) regs regs'.
Proof using All.
  intros fx regs m bs0 R0 KC0 KC1 H2 H8 H9 H13 H14 H16 H17 H28 H29 H30.
  dl_facts.
  ex_entry regs [sp; lineg; lined; w; j; rdv true 4 bs0] HR.
  assert (HK : know_ok SEGS (ex_env regs [sp; lineg; lined; w; j; rdv true 4 bs0]) m [KWord (SA (EVar 32) (12)) 4 (ELit 4); KWord (SA (EVar 32) (20)) 4 (EVar 35); KRange (EVar 32) 4096 140737488355328; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 1 20000; KRange (EVar 36) 0 19999]) by (ex_know regs).
  dl_run 400%nat [109732%Z; 109796%Z; 109820%Z] (SCR [] [EVar 37] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma bp4_1ac6cf : forall (fx : FPState) regs m (bs0 : list byte),
  branch_taken BC_NE (Z_to_bv 64 0) (getr regs 31) = false ->
  rdn SEGS m (Z_to_bv 64 (lined + (4 * (j / 32)))) 4 = Some bs0 ->
  store_ok SEGS m (Z_to_bv 64 (lined + (4 * (j / 32)))) 4 = true ->
  rdn SEGS m (Z_to_bv 64 (sp + 12)) 4 = Some (Z_to_le_bytes 4 4) ->
  rdn SEGS m (Z_to_bv 64 (sp + 20)) 4 = Some (Z_to_le_bytes 4 w) ->
  getr regs 2 = Z_to_bv 64 sp ->
  getr regs 8 = Z_to_bv 64 2 ->
  getr regs 9 = Z_to_bv 64 1 ->
  getr regs 13 = Z_to_bv 64 4 ->
  getr regs 14 = Z_to_bv 64 0 ->
  getr regs 16 = Z_to_bv 64 8 ->
  getr regs 17 = Z_to_bv 64 lineg ->
  getr regs 28 = Z_to_bv 64 j ->
  getr regs 29 = Z_to_bv 64 lineg ->
  getr regs 30 = Z_to_bv 64 lined ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1ad68) m rom) (@mkst fx regs' (Z_to_bv 64 0x1ace4) m' rom)
    /\ mframe [((lined + (4 * (j / 32)))%Z, 4%Z)] m m'
    /\ getr regs' 31 = Z_to_bv 64 (lined + (4 * (j / 32)))
    /\ regs_agree (fun r => In r [21; 22; 31]%list) regs regs'.
Proof using All.
  intros fx regs m bs0 BT R0 S0 KC0 KC1 H2 H8 H9 H13 H14 H16 H17 H28 H29 H30.
  dl_facts.
  ex_entry regs [sp; lineg; lined; w; j; rdv true 4 bs0] HR.
  assert (HK : know_ok SEGS (ex_env regs [sp; lineg; lined; w; j; rdv true 4 bs0]) m [KWord (SA (EVar 32) (12)) 4 (ELit 4); KWord (SA (EVar 32) (20)) 4 (EVar 35); KRange (EVar 32) 4096 140737488355328; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 1 20000; KRange (EVar 36) 0 19999]) by (ex_know regs).
  dl_run 400%nat [109732%Z; 109796%Z; 109820%Z] (SCR [false] [EVar 37] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma bp4_1ac6ct : forall (fx : FPState) regs m ,
  branch_taken BC_NE (Z_to_bv 64 0) (getr regs 31) = true ->
  rdn SEGS m (Z_to_bv 64 (sp + 12)) 4 = Some (Z_to_le_bytes 4 4) ->
  rdn SEGS m (Z_to_bv 64 (sp + 20)) 4 = Some (Z_to_le_bytes 4 w) ->
  getr regs 2 = Z_to_bv 64 sp ->
  getr regs 8 = Z_to_bv 64 2 ->
  getr regs 9 = Z_to_bv 64 1 ->
  getr regs 13 = Z_to_bv 64 4 ->
  getr regs 14 = Z_to_bv 64 0 ->
  getr regs 16 = Z_to_bv 64 8 ->
  getr regs 17 = Z_to_bv 64 lineg ->
  getr regs 28 = Z_to_bv 64 j ->
  getr regs 29 = Z_to_bv 64 lineg ->
  getr regs 30 = Z_to_bv 64 lined ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1ad68) m rom) (@mkst fx regs' (Z_to_bv 64 0x1ace4) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r []%list) regs regs'.
Proof using All.
  intros fx regs m  BT KC0 KC1 H2 H8 H9 H13 H14 H16 H17 H28 H29 H30.
  dl_facts.
  ex_entry regs [sp; lineg; lined; w; j] HR.
  assert (HK : know_ok SEGS (ex_env regs [sp; lineg; lined; w; j]) m [KWord (SA (EVar 32) (12)) 4 (ELit 4); KWord (SA (EVar 32) (20)) 4 (EVar 35); KRange (EVar 32) 4096 140737488355328; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 1 20000; KRange (EVar 36) 0 19999]) by (ex_know regs).
  dl_run 400%nat [109732%Z; 109796%Z; 109820%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Local Abbreviation bp4_1ac00_cells := (bp4_1ac00_cells_def sp lineg lined w j wplg wpld).
Local Abbreviation bp4_1ac00_cells_w := (bp4_1ac00_cells_w_def sp lineg lined w j wplg wpld).
Lemma bp4_1ac00_path : forall (fx : FPState) regs m,
  cells_ok SEGS m bp4_1ac00_cells ->
  (forall m', mframe bp4_1ac00_cells_w m m' -> rdn SEGS m' (Z_to_bv 64 (sp + 12)) 4 = Some (Z_to_le_bytes 4 4)) ->
  (forall m', mframe bp4_1ac00_cells_w m m' -> rdn SEGS m' (Z_to_bv 64 (sp + 20)) 4 = Some (Z_to_le_bytes 4 w)) ->
  getr regs 2 = Z_to_bv 64 sp ->
  getr regs 8 = Z_to_bv 64 2 ->
  getr regs 9 = Z_to_bv 64 1 ->
  getr regs 13 = Z_to_bv 64 4 ->
  getr regs 14 = Z_to_bv 64 0 ->
  getr regs 16 = Z_to_bv 64 8 ->
  getr regs 17 = Z_to_bv 64 lineg ->
  getr regs 28 = Z_to_bv 64 j ->
  getr regs 29 = Z_to_bv 64 lineg ->
  getr regs 30 = Z_to_bv 64 lined ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1acfc) m rom) (@mkst fx regs' (Z_to_bv 64 0x1ace4) m' rom)
    /\ mframe bp4_1ac00_cells m m'
    /\ mframe bp4_1ac00_cells_w m m'
    /\ regs_agree (fun r => In r [21; 22; 31]%list) regs regs'.
Proof using All.
  intros fx regs m CK  KCM0 KCM1 H2 H8 H9 H13 H14 H16 H17 H28 H29 H30.
  pose proof (mframe_refl bp4_1ac00_cells m) as FK0.
  pose proof (mframe_refl bp4_1ac00_cells_w m) as FW0.
  destruct (cells_ok_read SEGS m m bp4_1ac00_cells (lineg + (4 * (j / 8)))%Z 4%Z wr_readable_img CK (proj1 FK0) ltac:(dl_in0)) as [bs1_0 Rd1_0].
  destruct (bp4_1ac00 fx regs m bs1_0 Rd1_0 (KCM0 m FW0) (KCM1 m FW0) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r1 & m1 & RUN1 & FR1 & AG1).
  assert (FK1 : mframe bp4_1ac00_cells m m1) by (apply (mframe_step _ _ _ _ _ FK0 FR1); unfold bp4_1ac00_cells_def; dl_incl).
  assert (FW1 : mframe bp4_1ac00_cells_w m m1) by (apply (mframe_step _ _ _ _ _ FW0 FR1); unfold bp4_1ac00_cells_w_def; dl_incl).
  destruct (branch_taken BC_NE (Z_to_bv 64 0) (getr r1 31)) eqn:B1.
  - (* [comment removed for export] *)
    destruct (bp4_1ac6ct fx r1 m1  B1 (KCM0 m1 FW1) (KCM1 m1 FW1) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r2 & m2 & RUN2 & FR2 & AG2).
    assert (FK2 : mframe bp4_1ac00_cells m m2) by (apply (mframe_step _ _ _ _ _ FK1 FR2); unfold bp4_1ac00_cells_def; dl_incl).
    assert (FW2 : mframe bp4_1ac00_cells_w m m2) by (apply (mframe_step _ _ _ _ _ FW1 FR2); unfold bp4_1ac00_cells_w_def; dl_incl).
    exists r2, m2. split; [exact (msteps_trans _ _ _ _ RUN1 RUN2)|]. split; [exact FK2|]. split; [exact FW2|].
    repeat split; [dl_get .. | ra_chain].
  - (* [comment removed for export] *)
    destruct (cells_ok_read SEGS m m1 bp4_1ac00_cells (lined + (4 * (j / 32)))%Z 4%Z wr_readable_img CK (proj1 FK1) ltac:(dl_in0)) as [bs2_0 Rd2_0].
    destruct (bp4_1ac6cf fx r1 m1 bs2_0 B1 Rd2_0 (cells_ok_sok SEGS m m1 bp4_1ac00_cells (lined + (4 * (j / 32)))%Z 4%Z CK (proj1 FK1) ltac:(dl_in0)) (KCM0 m1 FW1) (KCM1 m1 FW1) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r2 & m2 & RUN2 & FR2 & E2_31 & AG2).
    assert (FK2 : mframe bp4_1ac00_cells m m2) by (apply (mframe_step _ _ _ _ _ FK1 FR2); unfold bp4_1ac00_cells_def; dl_incl).
    assert (FW2 : mframe bp4_1ac00_cells_w m m2) by (apply (mframe_step _ _ _ _ _ FW1 FR2); unfold bp4_1ac00_cells_w_def; dl_incl).
    exists r2, m2. split; [exact (msteps_trans _ _ _ _ RUN1 RUN2)|]. split; [exact FK2|]. split; [exact FW2|].
    repeat split; [dl_get .. | ra_chain].
Qed.

End BP4.
End O15BandPix4.

Module O15BandPix8.
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
Import OSSVerify.leptonica.grayquant_fuzzer.images.Plain.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.StepTac.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.StoreOk.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.StartupTac.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.Amb.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymExec2.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymExec2Sound.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymRun.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymDrive.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.WalksLib.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.W2Lib.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptStructs.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptExec.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.DitherLib.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.DitherTac.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.DitherLib2.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.DitherTac2.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.DitherTab.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.DitherTab1.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.BandLib.
(* [comment removed for export] *)







Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.

Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Abbreviation SEGS := Plain.M.loaded_segments.

Lemma wr_readable_img : wr_readable SEGS.
Proof.
  intros seg Hin Hwr. cbn in Hin.
  repeat (destruct Hin as [<-|Hin]; [first [reflexivity | discriminate Hwr] |]). destruct Hin.
Qed.

Definition bp8_1ac00_cells_def (sp lineg lined w j wplg wpld : Z) : list (Z * Z) := [((bytea (lineg + j))%Z, 1%Z); ((lined + (4 * (j / 32)))%Z, 4%Z)].
Definition bp8_1ac00_cells_w_def (sp lineg lined w j wplg wpld : Z) : list (Z * Z) := [((lined + (4 * (j / 32)))%Z, 4%Z)].
(* [comment removed for export] *)
Definition bp8_hyps (sp lineg lined w j wplg wpld : Z) : Prop :=
  (4096 <= sp <= 140737488355328)%Z /\ (4096 <= lineg <= 140737488355328)%Z /\ (lineg mod 4 = 0)%Z /\ (4096 <= lined <= 140737488355328)%Z /\ (lined mod 4 = 0)%Z /\ (1 <= w <= 20000)%Z /\ (0 <= j <= 19999)%Z /\ (0 <= j < w)%Z /\ (w * 8 <= 32 * wplg)%Z /\ (w <= 32 * wpld)%Z /\ dapart lined (4 * wpld) sp 96.
Section BP8.
Variable rom : word -> option byte.
Variables (sp lineg lined w j wplg wpld : Z).
Hypothesis HYP : bp8_hyps sp lineg lined w j wplg wpld.
Ltac dl_facts := pose proof HYP as (R_sp & R_lineg & A_lineg & R_lined & A_lined & R_w & R_j & Hj & Hwg & Hwd & AP_df); pose proof (dl_div_bounds j 32 ltac:(lia) ltac:(lia)) as DJ; pose proof (dl_div_bounds j 16 ltac:(lia) ltac:(lia)) as DJ16; pose proof (dl_div_bounds j 8 ltac:(lia) ltac:(lia)) as DJ8; destruct (al4_ex _ A_lined) as [cd Ecd]; destruct (al4_ex _ A_lineg) as [cs Ecs].
(* [comment removed for export] *)
Lemma bp8_1abe8 : forall (fx : FPState) regs m ,
  rdn SEGS m (Z_to_bv 64 (sp + 12)) 4 = Some (Z_to_le_bytes 4 8) ->
  rdn SEGS m (Z_to_bv 64 (sp + 20)) 4 = Some (Z_to_le_bytes 4 w) ->
  getr regs 2 = Z_to_bv 64 sp ->
  getr regs 28 = Z_to_bv 64 j ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1ace4) m rom) (@mkst fx regs' (Z_to_bv 64 0x1acf8) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 28 = Z_to_bv 64 (j + 1)
    /\ getr regs' 31 = Z_to_bv 64 w
    /\ regs_agree (fun r => In r [5; 6; 7; 28; 31]%list) regs regs'.
Proof using All.
  intros fx regs m  KC0 KC1 H2 H28.
  dl_facts.
  ex_entry regs [sp; lineg; lined; w; j] HR.
  assert (HK : know_ok SEGS (ex_env regs [sp; lineg; lined; w; j]) m [KWord (SA (EVar 32) (12)) 4 (ELit 8); KWord (SA (EVar 32) (20)) 4 (EVar 35); KRange (EVar 32) 4096 140737488355328; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 1 20000; KRange (EVar 36) 0 19999]) by (ex_know regs).
  dl_run 400%nat [109732%Z; 109796%Z; 109820%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma bp8_1abfcf : forall (fx : FPState) regs m ,
  branch_taken BC_GE (Z_to_bv 64 (j + 1)) (Z_to_bv 64 w) = false ->
  rdn SEGS m (Z_to_bv 64 (sp + 12)) 4 = Some (Z_to_le_bytes 4 8) ->
  rdn SEGS m (Z_to_bv 64 (sp + 20)) 4 = Some (Z_to_le_bytes 4 w) ->
  getr regs 2 = Z_to_bv 64 sp ->
  getr regs 28 = Z_to_bv 64 (j + 1) ->
  getr regs 31 = Z_to_bv 64 w ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1acf8) m rom) (@mkst fx regs' (Z_to_bv 64 0x1acfc) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r []%list) regs regs'.
Proof using All.
  intros fx regs m  BT KC0 KC1 H2 H28 H31.
  dl_facts.
  ex_entry regs [sp; lineg; lined; w; j] HR.
  assert (HK : know_ok SEGS (ex_env regs [sp; lineg; lined; w; j]) m [KWord (SA (EVar 32) (12)) 4 (ELit 8); KWord (SA (EVar 32) (20)) 4 (EVar 35); KRange (EVar 32) 4096 140737488355328; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 1 20000; KRange (EVar 36) 0 19999]) by (ex_know regs).
  dl_run 400%nat [109732%Z; 109796%Z; 109820%Z] (SCR [false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma bp8_1abfct : forall (fx : FPState) regs m ,
  branch_taken BC_GE (Z_to_bv 64 (j + 1)) (Z_to_bv 64 w) = true ->
  rdn SEGS m (Z_to_bv 64 (sp + 12)) 4 = Some (Z_to_le_bytes 4 8) ->
  rdn SEGS m (Z_to_bv 64 (sp + 20)) 4 = Some (Z_to_le_bytes 4 w) ->
  getr regs 2 = Z_to_bv 64 sp ->
  getr regs 28 = Z_to_bv 64 (j + 1) ->
  getr regs 31 = Z_to_bv 64 w ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1acf8) m rom) (@mkst fx regs' (Z_to_bv 64 0x1aca4) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r []%list) regs regs'.
Proof using All.
  intros fx regs m  BT KC0 KC1 H2 H28 H31.
  dl_facts.
  ex_entry regs [sp; lineg; lined; w; j] HR.
  assert (HK : know_ok SEGS (ex_env regs [sp; lineg; lined; w; j]) m [KWord (SA (EVar 32) (12)) 4 (ELit 8); KWord (SA (EVar 32) (20)) 4 (EVar 35); KRange (EVar 32) 4096 140737488355328; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 1 20000; KRange (EVar 36) 0 19999]) by (ex_know regs).
  dl_run 400%nat [109732%Z; 109796%Z; 109820%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma bp8_1ac00 : forall (fx : FPState) regs m (bs0 : list byte),
  rdn SEGS m (Z_to_bv 64 (bytea (lineg + j))) 1 = Some bs0 ->
  rdn SEGS m (Z_to_bv 64 (sp + 12)) 4 = Some (Z_to_le_bytes 4 8) ->
  rdn SEGS m (Z_to_bv 64 (sp + 20)) 4 = Some (Z_to_le_bytes 4 w) ->
  getr regs 2 = Z_to_bv 64 sp ->
  getr regs 8 = Z_to_bv 64 2 ->
  getr regs 9 = Z_to_bv 64 1 ->
  getr regs 13 = Z_to_bv 64 4 ->
  getr regs 14 = Z_to_bv 64 0 ->
  getr regs 16 = Z_to_bv 64 8 ->
  getr regs 17 = Z_to_bv 64 lineg ->
  getr regs 28 = Z_to_bv 64 j ->
  getr regs 29 = Z_to_bv 64 lineg ->
  getr regs 30 = Z_to_bv 64 lined ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1acfc) m rom) (@mkst fx regs' (Z_to_bv 64 0x1ad68) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r [21; 31]%list) regs regs'.
Proof using All.
  intros fx regs m bs0 R0 KC0 KC1 H2 H8 H9 H13 H14 H16 H17 H28 H29 H30.
  dl_facts.
  ex_entry regs [sp; lineg; lined; w; j; rdv false 1 bs0] HR.
  assert (HK : know_ok SEGS (ex_env regs [sp; lineg; lined; w; j; rdv false 1 bs0]) m [KWord (SA (EVar 32) (12)) 4 (ELit 8); KWord (SA (EVar 32) (20)) 4 (EVar 35); KRange (EVar 32) 4096 140737488355328; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 1 20000; KRange (EVar 36) 0 19999]) by (ex_know regs).
  dl_run 400%nat [109732%Z; 109796%Z; 109820%Z] (SCR [] [EVar 37] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma bp8_1ac6cf : forall (fx : FPState) regs m (bs0 : list byte),
  branch_taken BC_NE (Z_to_bv 64 0) (getr regs 31) = false ->
  rdn SEGS m (Z_to_bv 64 (lined + (4 * (j / 32)))) 4 = Some bs0 ->
  store_ok SEGS m (Z_to_bv 64 (lined + (4 * (j / 32)))) 4 = true ->
  rdn SEGS m (Z_to_bv 64 (sp + 12)) 4 = Some (Z_to_le_bytes 4 8) ->
  rdn SEGS m (Z_to_bv 64 (sp + 20)) 4 = Some (Z_to_le_bytes 4 w) ->
  getr regs 2 = Z_to_bv 64 sp ->
  getr regs 8 = Z_to_bv 64 2 ->
  getr regs 9 = Z_to_bv 64 1 ->
  getr regs 13 = Z_to_bv 64 4 ->
  getr regs 14 = Z_to_bv 64 0 ->
  getr regs 16 = Z_to_bv 64 8 ->
  getr regs 17 = Z_to_bv 64 lineg ->
  getr regs 28 = Z_to_bv 64 j ->
  getr regs 29 = Z_to_bv 64 lineg ->
  getr regs 30 = Z_to_bv 64 lined ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1ad68) m rom) (@mkst fx regs' (Z_to_bv 64 0x1ace4) m' rom)
    /\ mframe [((lined + (4 * (j / 32)))%Z, 4%Z)] m m'
    /\ getr regs' 31 = Z_to_bv 64 (lined + (4 * (j / 32)))
    /\ regs_agree (fun r => In r [21; 22; 31]%list) regs regs'.
Proof using All.
  intros fx regs m bs0 BT R0 S0 KC0 KC1 H2 H8 H9 H13 H14 H16 H17 H28 H29 H30.
  dl_facts.
  ex_entry regs [sp; lineg; lined; w; j; rdv true 4 bs0] HR.
  assert (HK : know_ok SEGS (ex_env regs [sp; lineg; lined; w; j; rdv true 4 bs0]) m [KWord (SA (EVar 32) (12)) 4 (ELit 8); KWord (SA (EVar 32) (20)) 4 (EVar 35); KRange (EVar 32) 4096 140737488355328; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 1 20000; KRange (EVar 36) 0 19999]) by (ex_know regs).
  dl_run 400%nat [109732%Z; 109796%Z; 109820%Z] (SCR [false] [EVar 37] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma bp8_1ac6ct : forall (fx : FPState) regs m ,
  branch_taken BC_NE (Z_to_bv 64 0) (getr regs 31) = true ->
  rdn SEGS m (Z_to_bv 64 (sp + 12)) 4 = Some (Z_to_le_bytes 4 8) ->
  rdn SEGS m (Z_to_bv 64 (sp + 20)) 4 = Some (Z_to_le_bytes 4 w) ->
  getr regs 2 = Z_to_bv 64 sp ->
  getr regs 8 = Z_to_bv 64 2 ->
  getr regs 9 = Z_to_bv 64 1 ->
  getr regs 13 = Z_to_bv 64 4 ->
  getr regs 14 = Z_to_bv 64 0 ->
  getr regs 16 = Z_to_bv 64 8 ->
  getr regs 17 = Z_to_bv 64 lineg ->
  getr regs 28 = Z_to_bv 64 j ->
  getr regs 29 = Z_to_bv 64 lineg ->
  getr regs 30 = Z_to_bv 64 lined ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1ad68) m rom) (@mkst fx regs' (Z_to_bv 64 0x1ace4) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r []%list) regs regs'.
Proof using All.
  intros fx regs m  BT KC0 KC1 H2 H8 H9 H13 H14 H16 H17 H28 H29 H30.
  dl_facts.
  ex_entry regs [sp; lineg; lined; w; j] HR.
  assert (HK : know_ok SEGS (ex_env regs [sp; lineg; lined; w; j]) m [KWord (SA (EVar 32) (12)) 4 (ELit 8); KWord (SA (EVar 32) (20)) 4 (EVar 35); KRange (EVar 32) 4096 140737488355328; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 1 20000; KRange (EVar 36) 0 19999]) by (ex_know regs).
  dl_run 400%nat [109732%Z; 109796%Z; 109820%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Local Abbreviation bp8_1ac00_cells := (bp8_1ac00_cells_def sp lineg lined w j wplg wpld).
Local Abbreviation bp8_1ac00_cells_w := (bp8_1ac00_cells_w_def sp lineg lined w j wplg wpld).
Lemma bp8_1ac00_path : forall (fx : FPState) regs m,
  cells_ok SEGS m bp8_1ac00_cells ->
  (forall m', mframe bp8_1ac00_cells_w m m' -> rdn SEGS m' (Z_to_bv 64 (sp + 12)) 4 = Some (Z_to_le_bytes 4 8)) ->
  (forall m', mframe bp8_1ac00_cells_w m m' -> rdn SEGS m' (Z_to_bv 64 (sp + 20)) 4 = Some (Z_to_le_bytes 4 w)) ->
  getr regs 2 = Z_to_bv 64 sp ->
  getr regs 8 = Z_to_bv 64 2 ->
  getr regs 9 = Z_to_bv 64 1 ->
  getr regs 13 = Z_to_bv 64 4 ->
  getr regs 14 = Z_to_bv 64 0 ->
  getr regs 16 = Z_to_bv 64 8 ->
  getr regs 17 = Z_to_bv 64 lineg ->
  getr regs 28 = Z_to_bv 64 j ->
  getr regs 29 = Z_to_bv 64 lineg ->
  getr regs 30 = Z_to_bv 64 lined ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1acfc) m rom) (@mkst fx regs' (Z_to_bv 64 0x1ace4) m' rom)
    /\ mframe bp8_1ac00_cells m m'
    /\ mframe bp8_1ac00_cells_w m m'
    /\ regs_agree (fun r => In r [21; 22; 31]%list) regs regs'.
Proof using All.
  intros fx regs m CK  KCM0 KCM1 H2 H8 H9 H13 H14 H16 H17 H28 H29 H30.
  pose proof (mframe_refl bp8_1ac00_cells m) as FK0.
  pose proof (mframe_refl bp8_1ac00_cells_w m) as FW0.
  destruct (cells_ok_read SEGS m m bp8_1ac00_cells (bytea (lineg + j))%Z 1%Z wr_readable_img CK (proj1 FK0) ltac:(dl_in0)) as [bs1_0 Rd1_0].
  destruct (bp8_1ac00 fx regs m bs1_0 Rd1_0 (KCM0 m FW0) (KCM1 m FW0) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r1 & m1 & RUN1 & FR1 & AG1).
  assert (FK1 : mframe bp8_1ac00_cells m m1) by (apply (mframe_step _ _ _ _ _ FK0 FR1); unfold bp8_1ac00_cells_def; dl_incl).
  assert (FW1 : mframe bp8_1ac00_cells_w m m1) by (apply (mframe_step _ _ _ _ _ FW0 FR1); unfold bp8_1ac00_cells_w_def; dl_incl).
  destruct (branch_taken BC_NE (Z_to_bv 64 0) (getr r1 31)) eqn:B1.
  - (* [comment removed for export] *)
    destruct (bp8_1ac6ct fx r1 m1  B1 (KCM0 m1 FW1) (KCM1 m1 FW1) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r2 & m2 & RUN2 & FR2 & AG2).
    assert (FK2 : mframe bp8_1ac00_cells m m2) by (apply (mframe_step _ _ _ _ _ FK1 FR2); unfold bp8_1ac00_cells_def; dl_incl).
    assert (FW2 : mframe bp8_1ac00_cells_w m m2) by (apply (mframe_step _ _ _ _ _ FW1 FR2); unfold bp8_1ac00_cells_w_def; dl_incl).
    exists r2, m2. split; [exact (msteps_trans _ _ _ _ RUN1 RUN2)|]. split; [exact FK2|]. split; [exact FW2|].
    repeat split; [dl_get .. | ra_chain].
  - (* [comment removed for export] *)
    destruct (cells_ok_read SEGS m m1 bp8_1ac00_cells (lined + (4 * (j / 32)))%Z 4%Z wr_readable_img CK (proj1 FK1) ltac:(dl_in0)) as [bs2_0 Rd2_0].
    destruct (bp8_1ac6cf fx r1 m1 bs2_0 B1 Rd2_0 (cells_ok_sok SEGS m m1 bp8_1ac00_cells (lined + (4 * (j / 32)))%Z 4%Z CK (proj1 FK1) ltac:(dl_in0)) (KCM0 m1 FW1) (KCM1 m1 FW1) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r2 & m2 & RUN2 & FR2 & E2_31 & AG2).
    assert (FK2 : mframe bp8_1ac00_cells m m2) by (apply (mframe_step _ _ _ _ _ FK1 FR2); unfold bp8_1ac00_cells_def; dl_incl).
    assert (FW2 : mframe bp8_1ac00_cells_w m m2) by (apply (mframe_step _ _ _ _ _ FW1 FR2); unfold bp8_1ac00_cells_w_def; dl_incl).
    exists r2, m2. split; [exact (msteps_trans _ _ _ _ RUN1 RUN2)|]. split; [exact FK2|]. split; [exact FW2|].
    repeat split; [dl_get .. | ra_chain].
Qed.

End BP8.
End O15BandPix8.

From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require MemSplit.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require FPSteps.
Module O15LeptQFill.
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
Import OSSVerify.leptonica.grayquant_fuzzer.images.Plain.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.StepTac.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.StoreOk.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.MemSplit.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.FPSteps.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.Amb.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymExec2.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymExec2Sound.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymRun.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymDrive.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.WalksLib.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptStructs.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptExec.
(* [comment removed for export] *)







Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Abbreviation SEGS := Plain.M.loaded_segments.

Definition QF_HEAD : Z := 0x1c090.
Definition QF_EXIT : Z := 0x1c09c.

Section QFill.
Variable rom : word -> option byte.

(* [comment removed for export] *)
Lemma qfill_T : forall (fx : FPState) regs m (a b : Z),
  (0 <= a)%Z -> (a + 4 < b)%Z -> (b < 2 ^ 63)%Z -> store_ok SEGS m (Z_to_bv 64 a) 4 = true ->
  getr regs 10 = Z_to_bv 64 a -> getr regs 11 = Z_to_bv 64 b ->
  exists regs', msteps SEGS (@mkst fx regs (Z_to_bv 64 QF_HEAD) m rom)
                        (@mkst fx regs' (Z_to_bv 64 QF_HEAD) (wbytes m (Z_to_bv 64 a) (word_to_le_bytes 4 (getr regs 20))) rom)
    /\ getr regs' 10 = Z_to_bv 64 (a + 4) /\ regs_agree (fun r => In r [10%bv]) regs regs'.
Proof.
  intros fx regs m a b Ha Hab Hb SOK H10 H11. unfold QF_HEAD.
  ex_entry regs [a; b] HR.
  assert (HK : know_ok SEGS (ex_env regs [a; b]) m [KRange (EVar 32) 0 (2 ^ 63); KRange (EVar 33) 0 (2 ^ 63); KWr (SA (EVar 32) 0) 4]).
  { ex_know regs. }
  ex_run 10%nat [0x1c090%Z; 0x1c09c%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. split; [ex_mem regs Hms|]. split; [ex_reg regs HR' | ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma qfill_F : forall (fx : FPState) regs m (a b : Z),
  (0 <= a)%Z -> (a + 4 = b)%Z -> (b < 2 ^ 63)%Z -> store_ok SEGS m (Z_to_bv 64 a) 4 = true ->
  getr regs 10 = Z_to_bv 64 a -> getr regs 11 = Z_to_bv 64 b ->
  exists regs', msteps SEGS (@mkst fx regs (Z_to_bv 64 QF_HEAD) m rom)
                        (@mkst fx regs' (Z_to_bv 64 QF_EXIT) (wbytes m (Z_to_bv 64 a) (word_to_le_bytes 4 (getr regs 20))) rom)
    /\ getr regs' 10 = Z_to_bv 64 (a + 4) /\ regs_agree (fun r => In r [10%bv]) regs regs'.
Proof.
  intros fx regs m a b Ha Hab Hb SOK H10 H11. unfold QF_HEAD, QF_EXIT.
  ex_entry regs [a; b] HR.
  assert (HK : know_ok SEGS (ex_env regs [a; b]) m [KRange (EVar 32) 0 (2 ^ 63); KRange (EVar 33) 0 (2 ^ 63); KWr (SA (EVar 32) 0) 4]).
  { ex_know regs. }
  ex_run 10%nat [0x1c090%Z; 0x1c09c%Z] (SCR [false] [] []) HR HK R' HR' Hms.
  exists R'. split; [ex_mem regs Hms|]. split; [ex_reg regs HR' | ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma qfill_loop : forall (n : nat) (fx : FPState) regs m (a : Z),
  (0 <= a)%Z -> (a + 4 * Z.of_nat (S n) < 2 ^ 63)%Z -> store_ok SEGS m (Z_to_bv 64 a) (4 * S n) = true ->
  getr regs 10 = Z_to_bv 64 a -> getr regs 11 = Z_to_bv 64 (a + 4 * Z.of_nat (S n)) ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 QF_HEAD) m rom) (@mkst fx regs' (Z_to_bv 64 QF_EXIT) m' rom)
    /\ getr regs' 10 = Z_to_bv 64 (a + 4 * Z.of_nat (S n)) /\ regs_agree (fun r => In r [10%bv]) regs regs'
    /\ (forall x : word, ~ (a <= bv_unsigned x < a + 4 * Z.of_nat (S n))%Z -> m' x = m x) /\ mem_grows m m'.
Proof.
  induction n as [|n IH]; intros fx regs m a Ha Hb SOK H10 H11.
  - destruct (qfill_F fx regs m a (a + 4 * Z.of_nat 1) Ha ltac:(lia) Hb SOK H10 H11) as (R' & Hms & G10 & AG).
    exists R', (wbytes m (Z_to_bv 64 a) (word_to_le_bytes 4 (getr regs 20))). split; [exact Hms|]. split; [rewrite G10; f_equal; lia|]. split; [exact AG|]. split; [|apply wbytes_grows].
    intros x Hx. apply wbytes_outside; rewrite length_N_to_le_bytes, u_Z2bv by lia; lia.
  - assert (S4 : store_ok SEGS m (Z_to_bv 64 a) 4 = true).
    { apply (store_ok_sub SEGS m (Z_to_bv 64 a) (Z_to_bv 64 a) (4 * S (S n)) 4); rewrite ?u_Z2bv by lia; try lia. exact SOK. }
    destruct (qfill_T fx regs m a (a + 4 * Z.of_nat (S (S n))) Ha ltac:(lia) Hb S4 H10 H11) as (R1 & Hms1 & G10 & AG1).
    set (m1 := wbytes m (Z_to_bv 64 a) (word_to_le_bytes 4 (getr regs 20))) in *.
    assert (SOK1 : store_ok SEGS m1 (Z_to_bv 64 (a + 4)) (4 * S n) = true).
    { apply (store_ok_mono SEGS (4 * S n) m m1); [apply wbytes_grows|].
      apply (store_ok_sub SEGS m (Z_to_bv 64 a) (Z_to_bv 64 (a + 4)) (4 * S (S n)) (4 * S n)); rewrite ?u_Z2bv by lia; try lia. exact SOK. }
    assert (H11' : getr R1 11 = Z_to_bv 64 (a + 4 + 4 * Z.of_nat (S n))).
    { rewrite (AG1 11%bv) by (cbn [In]; intros [X|[]]; discriminate X). rewrite H11. f_equal. lia. }
    destruct (IH fx R1 m1 (a + 4)%Z ltac:(lia) ltac:(lia) SOK1 G10 H11') as (R' & m' & Hms2 & G10' & AG2 & FR & GR).
    exists R', m'. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|]. split; [rewrite G10'; f_equal; lia|].
    split; [eapply regs_agree_trans; [exact AG1 | exact AG2]|]. split.
    + intros x Hx. rewrite FR by lia. unfold m1. apply wbytes_outside; rewrite length_N_to_le_bytes, u_Z2bv by lia; lia.
    + eapply mem_grows_trans; [apply wbytes_grows | exact GR].
Qed.

(* [comment removed for export] *)
Lemma qfill_loopZ : forall (fx : FPState) regs m (a cnt : Z),
  (0 <= a)%Z -> (1 <= cnt)%Z -> (a + 4 * cnt < 2 ^ 63)%Z -> store_ok SEGS m (Z_to_bv 64 a) (Z.to_nat (4 * cnt)) = true ->
  getr regs 10 = Z_to_bv 64 a -> getr regs 11 = Z_to_bv 64 (a + 4 * cnt) ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 QF_HEAD) m rom) (@mkst fx regs' (Z_to_bv 64 QF_EXIT) m' rom)
    /\ getr regs' 10 = Z_to_bv 64 (a + 4 * cnt) /\ regs_agree (fun r => In r [10%bv]) regs regs'
    /\ (forall x : word, ~ (a <= bv_unsigned x < a + 4 * cnt)%Z -> m' x = m x) /\ mem_grows m m'.
Proof.
  intros fx regs m a cnt Ha Hc Hb SOK H10 H11.
  assert (EC : Z.of_nat (S (Z.to_nat (cnt - 1))) = cnt) by lia.
  assert (EN : (4 * S (Z.to_nat (cnt - 1)))%nat = Z.to_nat (4 * cnt)) by lia.
  pose proof (qfill_loop (Z.to_nat (cnt - 1)) fx regs m a Ha) as L. rewrite EC, EN in L. exact (L Hb SOK H10 H11).
Qed.
End QFill.
End O15LeptQFill.
