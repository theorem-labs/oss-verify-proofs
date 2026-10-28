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
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OssFuzzTheorems.leptonica.grayquant_fuzzer.images Require Ubsan.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require PropExec.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require CatExec.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require CatSim.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require StepTac.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Hoare.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require StoreOk.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require StartupTac.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require Amb.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require SymExec2.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require SymExec2Sound.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require SymRun.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require SymDrive.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require WalksLib.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require W2Lib.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptStructs.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptExec.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require DitherLib.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require DitherTac.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require DitherLib2.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require DitherTac2.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require DitherTab.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require DitherTab1.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require BandLib.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require LiaFast.
Module V15BandLoop.
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
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.StoreOk.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.StartupTac.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.Amb.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymExec2.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymExec2Sound.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymRun.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymDrive.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.WalksLib.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.W2Lib.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptStructs.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptExec.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.DitherLib.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.DitherTac.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.DitherLib2.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.DitherTac2.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.DitherTab.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.DitherTab1.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.BandLib.
(* [comment removed for export] *)







Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.

Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Abbreviation SEGS := Ubsan.M.loaded_segments.

Lemma wr_readable_img : wr_readable SEGS.
Proof.
  intros seg Hin Hwr. cbn in Hin.
  repeat (destruct Hin as [<-|Hin]; [first [reflexivity | discriminate Hwr] |]). destruct Hin.
Qed.

(* [comment removed for export] *)
Definition ba_hyps (sp datag datad h : Z) : Prop :=
  (4096 <= sp <= 140737488355328)%Z /\ (4096 <= datag <= 140737488355328)%Z /\ (datag mod 4 = 0)%Z /\ (4096 <= datad <= 140737488355328)%Z /\ (datad mod 4 = 0)%Z /\ (1 <= h <= 20000)%Z.
Section BA.
Variable rom : word -> option byte.
Variables (sp datag datad h : Z).
Hypothesis HYP : ba_hyps sp datag datad h.
Ltac dl_facts := pose proof HYP as (R_sp & R_datag & A_datag & R_datad & A_datad & R_h); idtac.
(* [comment removed for export] *)
Lemma ba_1c268 : forall (fx : FPState) regs m ,
  rdn SEGS m (Z_to_bv 64 (sp + 16)) 4 = Some (Z_to_le_bytes 4 h) ->
  getr regs 2 = Z_to_bv 64 sp ->
  getr regs 18 = Z_to_bv 64 datag ->
  getr regs 20 = Z_to_bv 64 datad ->
  getr regs 23 = Z_to_bv 64 1 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1c36c) m rom) (@mkst fx regs' (Z_to_bv 64 0x1c3b4) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 5 = Z_to_bv 64 8
    /\ getr regs' 6 = Z_to_bv 64 134217727
    /\ getr regs' 7 = Z_to_bv 64 3
    /\ getr regs' 11 = Z_to_bv 64 1
    /\ getr regs' 12 = Z_to_bv 64 0
    /\ getr regs' 13 = Z_to_bv 64 0
    /\ getr regs' 14 = Z_to_bv 64 1
    /\ getr regs' 15 = Z_to_bv 64 1
    /\ getr regs' 16 = Z_to_bv 64 4
    /\ getr regs' 17 = Z_to_bv 64 18446744071562067968
    /\ regs_agree (fun r => In r [5; 6; 7; 11; 12; 13; 14; 15; 16; 17]%list) regs regs'.
Proof using All.
  intros fx regs m  KC0 H2 H18 H20 H23.
  dl_facts.
  ex_entry regs [sp; datag; datad; h] HR.
  assert (HK : know_ok SEGS (ex_env regs [sp; datag; datad; h]) m [KWord (SA (EVar 32) (16)) 4 (EVar 35); KRange (EVar 32) 4096 140737488355328; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 1 20000]) by (ex_know regs).
  dl_run 400%nat [115636%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

End BA.

(* [comment removed for export] *)
Definition br_hyps (sp datag datad w h wplg wpld i acc : Z) : Prop :=
  (4096 <= sp <= 140737488355328)%Z /\ (4096 <= datag <= 140737488355328)%Z /\ (datag mod 4 = 0)%Z /\ (4096 <= datad <= 140737488355328)%Z /\ (datad mod 4 = 0)%Z /\ (1 <= w <= 20000)%Z /\ (1 <= h <= 20000)%Z /\ (1 <= wplg <= 5000)%Z /\ (1 <= wpld <= 5000)%Z /\ (0 <= i <= 19999)%Z /\ (0 <= acc <= 16777216)%Z /\ (acc = i * wplg)%Z /\ (0 <= i * wplg < 2 ^ 24)%Z /\ (0 <= i * wpld < 2 ^ 24)%Z.
Section BR.
Variable rom : word -> option byte.
Variables (sp datag datad w h wplg wpld i acc : Z).
Hypothesis HYP : br_hyps sp datag datad w h wplg wpld i acc.
Ltac dl_facts := pose proof HYP as (R_sp & R_datag & A_datag & R_datad & A_datad & R_w & R_h & R_wplg & R_wpld & R_i & R_acc & Ea & Hpg & Hpd); idtac.
(* [comment removed for export] *)
Lemma br_1c2b0 : forall (fx : FPState) regs m ,
  rdn SEGS m (Z_to_bv 64 (sp + 20)) 4 = Some (Z_to_le_bytes 4 w) ->
  getr regs 2 = Z_to_bv 64 sp ->
  getr regs 10 = Z_to_bv 64 wpld ->
  getr regs 12 = Z_to_bv 64 acc ->
  getr regs 13 = Z_to_bv 64 i ->
  getr regs 14 = Z_to_bv 64 1 ->
  getr regs 15 = Z_to_bv 64 1 ->
  getr regs 18 = Z_to_bv 64 datag ->
  getr regs 19 = Z_to_bv 64 wplg ->
  getr regs 20 = Z_to_bv 64 datad ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1c3b4) m rom) (@mkst fx regs' (Z_to_bv 64 0x1c468) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 21 = Z_to_bv 64 0
    /\ getr regs' 23 = Z_to_bv 64 0
    /\ getr regs' 24 = Z_to_bv 64 (datag + (4 * acc))
    /\ getr regs' 28 = Z_to_bv 64 (datag + (4 * (i * wplg)))
    /\ getr regs' 29 = Z_to_bv 64 (datad + (4 * (i * wpld)))
    /\ getr regs' 30 = Z_to_bv 64 0
    /\ getr regs' 31 = Z_to_bv 64 0
    /\ regs_agree (fun r => In r [21; 23; 24; 28; 29; 30; 31]%list) regs regs'.
Proof using All.
  intros fx regs m  KC0 H2 H10 H12 H13 H14 H15 H18 H19 H20.
  dl_facts.
  ex_entry regs [sp; datag; datad; w; h; wplg; wpld; i; acc] HR.
  assert (HK : know_ok SEGS (ex_env regs [sp; datag; datad; w; h; wplg; wpld; i; acc]) m [KWord (SA (EVar 32) (20)) 4 (EVar 35); KRange (EVar 32) 4096 140737488355328; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 1 20000; KRange (EVar 36) 1 20000; KRange (EVar 37) 1 5000; KRange (EVar 38) 1 5000; KRange (EVar 39) 0 19999; KRange (EVar 40) 0 16777216]) by (ex_know regs).
  dl_run 400%nat [115816%Z] (SCR [false; false; false; false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

End BR.

(* [comment removed for export] *)
Definition bl_hyps (sp datag datad w h wplg wpld i acc : Z) : Prop :=
  (4096 <= sp <= 140737488355328)%Z /\ (4096 <= datag <= 140737488355328)%Z /\ (datag mod 4 = 0)%Z /\ (4096 <= datad <= 140737488355328)%Z /\ (datad mod 4 = 0)%Z /\ (1 <= w <= 20000)%Z /\ (1 <= h <= 20000)%Z /\ (1 <= wplg <= 5000)%Z /\ (1 <= wpld <= 5000)%Z /\ (0 <= i <= 19999)%Z /\ (0 <= acc <= 16777216)%Z /\ (acc = i * wplg)%Z /\ (0 <= i * wplg < 2 ^ 24)%Z /\ (0 <= i * wpld < 2 ^ 24)%Z /\ (0 <= i < h)%Z.
Section BL.
Variable rom : word -> option byte.
Variables (sp datag datad w h wplg wpld i acc : Z).
Hypothesis HYP : bl_hyps sp datag datad w h wplg wpld i acc.
Ltac dl_facts := pose proof HYP as (R_sp & R_datag & A_datag & R_datad & A_datad & R_w & R_h & R_wplg & R_wpld & R_i & R_acc & Ea & Hpg & Hpd & Hi); idtac.
(* [comment removed for export] *)
Lemma bl_1c2a0 : forall (fx : FPState) regs m ,
  rdn SEGS m (Z_to_bv 64 (sp + 16)) 4 = Some (Z_to_le_bytes 4 h) ->
  getr regs 2 = Z_to_bv 64 sp ->
  getr regs 10 = Z_to_bv 64 wpld ->
  getr regs 12 = Z_to_bv 64 acc ->
  getr regs 13 = Z_to_bv 64 i ->
  getr regs 14 = Z_to_bv 64 1 ->
  getr regs 15 = Z_to_bv 64 1 ->
  getr regs 18 = Z_to_bv 64 datag ->
  getr regs 19 = Z_to_bv 64 wplg ->
  getr regs 20 = Z_to_bv 64 datad ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1c3a4) m rom) (@mkst fx regs' (Z_to_bv 64 0x1c3b0) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 12 = Z_to_bv 64 (acc + wplg)
    /\ getr regs' 13 = Z_to_bv 64 (i + 1)
    /\ getr regs' 28 = Z_to_bv 64 h
    /\ regs_agree (fun r => In r [12; 13; 28]%list) regs regs'.
Proof using All.
  intros fx regs m  KC0 H2 H10 H12 H13 H14 H15 H18 H19 H20.
  dl_facts.
  ex_entry regs [sp; datag; datad; w; h; wplg; wpld; i; acc; (acc + wplg)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [sp; datag; datad; w; h; wplg; wpld; i; acc; (acc + wplg)%Z]) m [KWord (SA (EVar 32) (16)) 4 (EVar 36); KRange (EVar 32) 4096 140737488355328; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 1 20000; KRange (EVar 36) 1 20000; KRange (EVar 37) 1 5000; KRange (EVar 38) 1 5000; KRange (EVar 39) 0 19999; KRange (EVar 40) 0 16777216; KRange (EVar 41) 1 16782216]) by (ex_know regs).
  dl_run 400%nat [115636%Z; 116064%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma bl_1c2acf : forall (fx : FPState) regs m ,
  branch_taken BC_GE (Z_to_bv 64 (i + 1)) (Z_to_bv 64 h) = false ->
  rdn SEGS m (Z_to_bv 64 (sp + 16)) 4 = Some (Z_to_le_bytes 4 h) ->
  getr regs 2 = Z_to_bv 64 sp ->
  getr regs 10 = Z_to_bv 64 wpld ->
  getr regs 12 = Z_to_bv 64 (acc + wplg) ->
  getr regs 13 = Z_to_bv 64 (i + 1) ->
  getr regs 14 = Z_to_bv 64 1 ->
  getr regs 15 = Z_to_bv 64 1 ->
  getr regs 18 = Z_to_bv 64 datag ->
  getr regs 19 = Z_to_bv 64 wplg ->
  getr regs 20 = Z_to_bv 64 datad ->
  getr regs 28 = Z_to_bv 64 h ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1c3b0) m rom) (@mkst fx regs' (Z_to_bv 64 0x1c3b4) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r []%list) regs regs'.
Proof using All.
  intros fx regs m  BT KC0 H2 H10 H12 H13 H14 H15 H18 H19 H20 H28.
  dl_facts.
  ex_entry regs [sp; datag; datad; w; h; wplg; wpld; i; acc; (acc + wplg)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [sp; datag; datad; w; h; wplg; wpld; i; acc; (acc + wplg)%Z]) m [KWord (SA (EVar 32) (16)) 4 (EVar 36); KRange (EVar 32) 4096 140737488355328; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 1 20000; KRange (EVar 36) 1 20000; KRange (EVar 37) 1 5000; KRange (EVar 38) 1 5000; KRange (EVar 39) 0 19999; KRange (EVar 40) 0 16777216; KRange (EVar 41) 1 16782216]) by (ex_know regs).
  dl_run 400%nat [115636%Z; 116064%Z] (SCR [false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma bl_1c2act : forall (fx : FPState) regs m ,
  branch_taken BC_GE (Z_to_bv 64 (i + 1)) (Z_to_bv 64 h) = true ->
  rdn SEGS m (Z_to_bv 64 (sp + 16)) 4 = Some (Z_to_le_bytes 4 h) ->
  getr regs 2 = Z_to_bv 64 sp ->
  getr regs 10 = Z_to_bv 64 wpld ->
  getr regs 12 = Z_to_bv 64 (acc + wplg) ->
  getr regs 13 = Z_to_bv 64 (i + 1) ->
  getr regs 14 = Z_to_bv 64 1 ->
  getr regs 15 = Z_to_bv 64 1 ->
  getr regs 18 = Z_to_bv 64 datag ->
  getr regs 19 = Z_to_bv 64 wplg ->
  getr regs 20 = Z_to_bv 64 datad ->
  getr regs 28 = Z_to_bv 64 h ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1c3b0) m rom) (@mkst fx regs' (Z_to_bv 64 0x1c560) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r []%list) regs regs'.
Proof using All.
  intros fx regs m  BT KC0 H2 H10 H12 H13 H14 H15 H18 H19 H20 H28.
  dl_facts.
  ex_entry regs [sp; datag; datad; w; h; wplg; wpld; i; acc; (acc + wplg)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [sp; datag; datad; w; h; wplg; wpld; i; acc; (acc + wplg)%Z]) m [KWord (SA (EVar 32) (16)) 4 (EVar 36); KRange (EVar 32) 4096 140737488355328; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 1 20000; KRange (EVar 36) 1 20000; KRange (EVar 37) 1 5000; KRange (EVar 38) 1 5000; KRange (EVar 39) 0 19999; KRange (EVar 40) 0 16777216; KRange (EVar 41) 1 16782216]) by (ex_know regs).
  dl_run 400%nat [115636%Z; 116064%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

End BL.
End V15BandLoop.

From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require WalkTac.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require SumsLib.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require SumWalkTac.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptDefs.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptArith.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptArith2.
Module V15LeptUb.
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
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CatExec.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CatSim.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.StepTac.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Hoare.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.StartupTac.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.WalkTac.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.SumsLib.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.SumWalkTac.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.WalksLib.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.W2Lib.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptDefs.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptArith.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptArith2.
(* [comment removed for export] *)





Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Lemma al16_mod8 : forall p, p mod 16 = 0 -> p mod 8 = 0.
Proof. intros p H. lia. Qed.
Lemma al16_mod4 : forall p, p mod 16 = 0 -> p mod 4 = 0.
Proof. intros p H. lia. Qed.
Lemma al8_mod4 : forall p, p mod 8 = 0 -> p mod 4 = 0.
Proof. intros p H. lia. Qed.
Lemma al16_plus_mod8 : forall p k, p mod 16 = 0 -> k mod 8 = 0 -> (p + k) mod 8 = 0.
Proof. intros p k H1 H2. lia. Qed.
Lemma al16_plus_mod4 : forall p k, p mod 16 = 0 -> k mod 4 = 0 -> (p + k) mod 4 = 0.
Proof. intros p k H1 H2. lia. Qed.
Lemma al4_plus_mod4 : forall p k, p mod 4 = 0 -> k mod 4 = 0 -> (p + k) mod 4 = 0.
Proof. intros p k H1 H2. lia. Qed.
Lemma sp_slot_al8 : forall sp k, sp mod 16 = 0 -> k mod 8 = 0 -> (sp - k) mod 8 = 0.
Proof. intros sp k H1 H2. lia. Qed.
Lemma sp_slot_al4' : forall sp k, sp mod 16 = 0 -> k mod 4 = 0 -> (sp - k) mod 4 = 0.
Proof. intros sp k H1 H2. lia. Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma zbv_or : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> v_or (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (Z.lor a b).
Proof. intros a b Ha Hb. unfold v_or. rewrite !u_Z2bv by lia. reflexivity. Qed.

Lemma Z_lor_range64 : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> 0 <= Z.lor a b < 2 ^ 64.
Proof.
  intros a b Ha Hb. split; [apply Z.lor_nonneg; lia|].
  destruct (Z.eq_dec (Z.lor a b) 0) as [->|NZ]; [lia|].
  apply Z.log2_lt_pow2; [pose proof (Z.lor_nonneg a b); lia|].
  rewrite Z.log2_lor by lia. apply Z.max_lub_lt.
  - destruct (Z.eq_dec a 0) as [->|]; [cbn; lia | apply Z.log2_lt_pow2; lia].
  - destruct (Z.eq_dec b 0) as [->|]; [cbn; lia | apply Z.log2_lt_pow2; lia].
Qed.

Lemma lor_mod_pow2_0 : forall a b n, 0 <= a -> 0 <= b -> 0 <= n -> a mod 2 ^ n = 0 -> b mod 2 ^ n = 0 -> (Z.lor a b) mod 2 ^ n = 0.
Proof.
  intros a b n Ha Hb Hn Ma Mb.
  rewrite <- Z.land_ones by lia. rewrite Z.land_lor_distr_l. rewrite !Z.land_ones by lia. rewrite Ma, Mb. reflexivity.
Qed.
Lemma lor_mod4_0 : forall a b, 0 <= a -> 0 <= b -> a mod 4 = 0 -> b mod 4 = 0 -> (Z.lor a b) mod 4 = 0.
Proof. intros a b Ha Hb Ma Mb. change 4 with (2 ^ 2) in *. apply lor_mod_pow2_0; lia || assumption. Qed.
Lemma lor_mod8_0 : forall a b, 0 <= a -> 0 <= b -> a mod 8 = 0 -> b mod 8 = 0 -> (Z.lor a b) mod 8 = 0.
Proof. intros a b Ha Hb Ma Mb. change 8 with (2 ^ 3) in *. apply lor_mod_pow2_0; lia || assumption. Qed.

(* [comment removed for export] *)
Ltac guard4 F D EQ := stepiv F D (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite andi_3; unorm; rewrite EQ; reflexivity).
Ltac guard8 F D EQ := stepiv F D (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite andi_7; unorm; rewrite EQ; reflexivity).
(* [comment removed for export] *)
Ltac orv F D a b :=
  chain_step;
  [ reflexivity
  | eapply step_or_at with (v := Z_to_bv 64 (Z.lor a b)); [ exact F | reflexivity | exact D | reflexivity | gres; pin; apply zbv_or; lia ]
  | step_simpl ].
End V15LeptUb.

Module V15QFillBlk.
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
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.StoreOk.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.StartupTac.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.Amb.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymExec2.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymExec2Sound.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymRun.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymDrive.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.WalksLib.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.W2Lib.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptStructs.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptExec.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.DitherLib.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.DitherTac.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.DitherLib2.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.DitherTac2.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.DitherTab.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.DitherTab1.
(* [comment removed for export] *)







Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.

Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Abbreviation SEGS := Ubsan.M.loaded_segments.

Lemma wr_readable_img : wr_readable SEGS.
Proof.
  intros seg Hin Hwr. cbn in Hin.
  repeat (destruct Hin as [<-|Hin]; [first [reflexivity | discriminate Hwr] |]). destruct Hin.
Qed.

(* [comment removed for export] *)
Definition qa_hyps (p j v : Z) : Prop :=
  (4096 <= p <= 140737488355328)%Z /\ (p mod 4 = 0)%Z /\ (0 <= j <= 255)%Z /\ (1 <= v <= 256)%Z /\ (j < v)%Z.
Section QA.
Variable rom : word -> option byte.
Variables (p j v : Z).
Hypothesis HYP : qa_hyps p j v.
Ltac dl_facts := pose proof HYP as (R_p & A_p & R_j & R_v & Hjv); idtac.
(* [comment removed for export] *)
Lemma qa_1dec4 : forall (fx : FPState) regs m ,
  store_ok SEGS m (Z_to_bv 64 (p + 4 * j)) 4 = true ->
  getr regs 9 = Z_to_bv 64 p ->
  getr regs 10 = Z_to_bv 64 (p + 4 * j) ->
  getr regs 11 = Z_to_bv 64 (p + 4 * j) ->
  getr regs 21 = Z_to_bv 64 1 ->
  getr regs 23 = Z_to_bv 64 v ->
  getr regs 24 = Z_to_bv 64 1 ->
  getr regs 25 = Z_to_bv 64 j ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1dfc8) m rom) (@mkst fx regs' (Z_to_bv 64 0x1dff8) m' rom)
    /\ mframe [((p + 4 * j)%Z, 4%Z)] m m'
    /\ getr regs' 10 = Z_to_bv 64 ((p + 4 * j) + 4)
    /\ getr regs' 11 = Z_to_bv 64 ((p + 4 * j) + 4)
    /\ getr regs' 13 = Z_to_bv 64 0
    /\ getr regs' 25 = Z_to_bv 64 (j + 1)
    /\ regs_agree (fun r => In r [10; 11; 12; 13; 25]%list) regs regs'.
Proof using All.
  intros fx regs m  S0 H9 H10 H11 H21 H23 H24 H25.
  dl_facts.
  ex_entry regs [p; j; v] HR.
  assert (HK : know_ok SEGS (ex_env regs [p; j; v]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 0 255; KRange (EVar 34) 1 256]) by (ex_know regs).
  dl_run 400%nat [122824%Z; 122876%Z] (SCR [false; false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma qa_1def4f : forall (fx : FPState) regs m ,
  branch_taken BC_LT (Z_to_bv 64 (j + 1)) (Z_to_bv 64 v) = false ->
  getr regs 9 = Z_to_bv 64 p ->
  getr regs 10 = Z_to_bv 64 ((p + 4 * j) + 4) ->
  getr regs 11 = Z_to_bv 64 ((p + 4 * j) + 4) ->
  getr regs 13 = Z_to_bv 64 0 ->
  getr regs 21 = Z_to_bv 64 1 ->
  getr regs 23 = Z_to_bv 64 v ->
  getr regs 24 = Z_to_bv 64 1 ->
  getr regs 25 = Z_to_bv 64 (j + 1) ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1dff8) m rom) (@mkst fx regs' (Z_to_bv 64 0x1dffc) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r []%list) regs regs'.
Proof using All.
  intros fx regs m  BT H9 H10 H11 H13 H21 H23 H24 H25.
  dl_facts.
  ex_entry regs [p; j; v] HR.
  assert (HK : know_ok SEGS (ex_env regs [p; j; v]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 0 255; KRange (EVar 34) 1 256]) by (ex_know regs).
  dl_run 400%nat [122824%Z; 122876%Z] (SCR [false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma qa_1def4t : forall (fx : FPState) regs m ,
  branch_taken BC_LT (Z_to_bv 64 (j + 1)) (Z_to_bv 64 v) = true ->
  getr regs 9 = Z_to_bv 64 p ->
  getr regs 10 = Z_to_bv 64 ((p + 4 * j) + 4) ->
  getr regs 11 = Z_to_bv 64 ((p + 4 * j) + 4) ->
  getr regs 13 = Z_to_bv 64 0 ->
  getr regs 21 = Z_to_bv 64 1 ->
  getr regs 23 = Z_to_bv 64 v ->
  getr regs 24 = Z_to_bv 64 1 ->
  getr regs 25 = Z_to_bv 64 (j + 1) ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1dff8) m rom) (@mkst fx regs' (Z_to_bv 64 0x1dfc8) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r []%list) regs regs'.
Proof using All.
  intros fx regs m  BT H9 H10 H11 H13 H21 H23 H24 H25.
  dl_facts.
  ex_entry regs [p; j; v] HR.
  assert (HK : know_ok SEGS (ex_env regs [p; j; v]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 0 255; KRange (EVar 34) 1 256]) by (ex_know regs).
  dl_run 400%nat [122824%Z; 122876%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

End QA.

(* [comment removed for export] *)
Definition qb_hyps (p j : Z) : Prop :=
  (4096 <= p <= 140737488355328)%Z /\ (p mod 4 = 0)%Z /\ (0 <= j <= 255)%Z.
Section QB.
Variable rom : word -> option byte.
Variables (p j : Z).
Hypothesis HYP : qb_hyps p j.
Ltac dl_facts := pose proof HYP as (R_p & A_p & R_j); idtac.
(* [comment removed for export] *)
Lemma qb_1dfd8 : forall (fx : FPState) regs m ,
  store_ok SEGS m (Z_to_bv 64 (p + 4 * j)) 4 = true ->
  getr regs 9 = Z_to_bv 64 p ->
  getr regs 10 = Z_to_bv 64 1 ->
  getr regs 11 = Z_to_bv 64 (p + 4 * j) ->
  getr regs 12 = Z_to_bv 64 256 ->
  getr regs 13 = Z_to_bv 64 (p + 4 * j) ->
  getr regs 21 = Z_to_bv 64 1 ->
  getr regs 23 = Z_to_bv 64 j ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1e0dc) m rom) (@mkst fx regs' (Z_to_bv 64 0x1e10c) m' rom)
    /\ mframe [((p + 4 * j)%Z, 4%Z)] m m'
    /\ getr regs' 11 = Z_to_bv 64 ((p + 4 * j) + 4)
    /\ getr regs' 13 = Z_to_bv 64 ((p + 4 * j) + 4)
    /\ getr regs' 15 = Z_to_bv 64 0
    /\ getr regs' 23 = Z_to_bv 64 (j + 1)
    /\ regs_agree (fun r => In r [11; 13; 14; 15; 23]%list) regs regs'.
Proof using All.
  intros fx regs m  S0 H9 H10 H11 H12 H13 H21 H23.
  dl_facts.
  ex_entry regs [p; j] HR.
  assert (HK : know_ok SEGS (ex_env regs [p; j]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 0 255]) by (ex_know regs).
  dl_run 400%nat [123100%Z; 123152%Z] (SCR [false; false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma qb_1e008f : forall (fx : FPState) regs m ,
  branch_taken BC_NE (Z_to_bv 64 (j + 1)) (Z_to_bv 64 256) = false ->
  getr regs 9 = Z_to_bv 64 p ->
  getr regs 10 = Z_to_bv 64 1 ->
  getr regs 11 = Z_to_bv 64 ((p + 4 * j) + 4) ->
  getr regs 12 = Z_to_bv 64 256 ->
  getr regs 13 = Z_to_bv 64 ((p + 4 * j) + 4) ->
  getr regs 15 = Z_to_bv 64 0 ->
  getr regs 21 = Z_to_bv 64 1 ->
  getr regs 23 = Z_to_bv 64 (j + 1) ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1e10c) m rom) (@mkst fx regs' (Z_to_bv 64 0x1e110) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r []%list) regs regs'.
Proof using All.
  intros fx regs m  BT H9 H10 H11 H12 H13 H15 H21 H23.
  dl_facts.
  ex_entry regs [p; j] HR.
  assert (HK : know_ok SEGS (ex_env regs [p; j]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 0 255]) by (ex_know regs).
  dl_run 400%nat [123100%Z; 123152%Z] (SCR [false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma qb_1e008t : forall (fx : FPState) regs m ,
  branch_taken BC_NE (Z_to_bv 64 (j + 1)) (Z_to_bv 64 256) = true ->
  getr regs 9 = Z_to_bv 64 p ->
  getr regs 10 = Z_to_bv 64 1 ->
  getr regs 11 = Z_to_bv 64 ((p + 4 * j) + 4) ->
  getr regs 12 = Z_to_bv 64 256 ->
  getr regs 13 = Z_to_bv 64 ((p + 4 * j) + 4) ->
  getr regs 15 = Z_to_bv 64 0 ->
  getr regs 21 = Z_to_bv 64 1 ->
  getr regs 23 = Z_to_bv 64 (j + 1) ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1e10c) m rom) (@mkst fx regs' (Z_to_bv 64 0x1e0dc) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r []%list) regs regs'.
Proof using All.
  intros fx regs m  BT H9 H10 H11 H12 H13 H15 H21 H23.
  dl_facts.
  ex_entry regs [p; j] HR.
  assert (HK : know_ok SEGS (ex_env regs [p; j]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 0 255]) by (ex_know regs).
  dl_run 400%nat [123100%Z; 123152%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

End QB.
End V15QFillBlk.
