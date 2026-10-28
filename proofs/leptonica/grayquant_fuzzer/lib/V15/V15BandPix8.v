(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.grayquant_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare StoreOk StartupTac.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import WalksLib W2Lib LeptStructs LeptExec DitherLib DitherTac DitherLib2 DitherTac2 DitherTab DitherTab1 BandLib.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require LiaFast.
Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Abbreviation SEGS := Ubsan.M.loaded_segments.

Lemma wr_readable_img : wr_readable SEGS.
Proof.
  intros seg Hin Hwr. cbn in Hin.
  repeat (destruct Hin as [<-|Hin]; [first [reflexivity | discriminate Hwr] |]). destruct Hin.
Qed.

Definition bp8_1c364_cells_def (sp datag datad lineg lined w j wplg wpld : Z) : list (Z * Z) := [((bytea (lineg + j))%Z, 1%Z); ((lined + (4 * (j / 32)))%Z, 4%Z)].
Definition bp8_1c364_cells_w_def (sp datag datad lineg lined w j wplg wpld : Z) : list (Z * Z) := [((lined + (4 * (j / 32)))%Z, 4%Z)].
(* [comment removed for export] *)
Definition bp8_hyps (sp datag datad lineg lined w j wplg wpld : Z) : Prop :=
  (4096 <= sp <= 140737488355328)%Z /\ (4096 <= datag <= 140737488355328)%Z /\ (datag mod 4 = 0)%Z /\ (4096 <= datad <= 140737488355328)%Z /\ (datad mod 4 = 0)%Z /\ (4096 <= lineg <= 140737488355328)%Z /\ (lineg mod 4 = 0)%Z /\ (4096 <= lined <= 140737488355328)%Z /\ (lined mod 4 = 0)%Z /\ (1 <= w <= 20000)%Z /\ (0 <= j <= 19999)%Z /\ (0 <= j < w)%Z /\ (w * 8 <= 32 * wplg)%Z /\ (w <= 32 * wpld)%Z /\ dapart lined (4 * wpld) sp 128.
Section BP8.
Variable rom : word -> option byte.
Variables (sp datag datad lineg lined w j wplg wpld : Z).
Hypothesis HYP : bp8_hyps sp datag datad lineg lined w j wplg wpld.
Ltac dl_facts := pose proof HYP as (R_sp & R_datag & A_datag & R_datad & A_datad & R_lineg & A_lineg & R_lined & A_lined & R_w & R_j & Hj & Hwg & Hwd & AP_df); pose proof (dl_div_bounds j 32 ltac:(lia) ltac:(lia)) as DJ; pose proof (dl_div_bounds j 16 ltac:(lia) ltac:(lia)) as DJ16; pose proof (dl_div_bounds j 8 ltac:(lia) ltac:(lia)) as DJ8; destruct (al4_ex _ A_lined) as [cd Ecd]; destruct (al4_ex _ A_lineg) as [cs Ecs].
(* [comment removed for export] *)
Lemma bp8_1c34c : forall (fx : FPState) regs m ,
  rdn SEGS m (Z_to_bv 64 (sp + 12)) 4 = Some (Z_to_le_bytes 4 8) ->
  rdn SEGS m (Z_to_bv 64 (sp + 20)) 4 = Some (Z_to_le_bytes 4 w) ->
  getr regs 2 = Z_to_bv 64 sp ->
  getr regs 23 = Z_to_bv 64 j ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1c450) m rom) (@mkst fx regs' (Z_to_bv 64 0x1c464) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 23 = Z_to_bv 64 (j + 1)
    /\ getr regs' 25 = Z_to_bv 64 w
    /\ regs_agree (fun r => In r [21; 23; 25; 30; 31]%list) regs regs'.
Proof using All.
  intros fx regs m  KC0 KC1 H2 H23.
  dl_facts.
  ex_entry regs [sp; datag; datad; lineg; lined; w; j] HR.
  assert (HK : know_ok SEGS (ex_env regs [sp; datag; datad; lineg; lined; w; j]) m [KWord (SA (EVar 32) (12)) 4 (ELit 8); KWord (SA (EVar 32) (20)) 4 (EVar 37); KRange (EVar 32) 4096 140737488355328; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488355328; KAlign (EVar 36) 4; KRange (EVar 37) 1 20000; KRange (EVar 38) 0 19999]) by (ex_know regs).
  dl_run 400%nat [115620%Z; 115792%Z; 115816%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma bp8_1c360f : forall (fx : FPState) regs m ,
  branch_taken BC_GE (Z_to_bv 64 (j + 1)) (Z_to_bv 64 w) = false ->
  rdn SEGS m (Z_to_bv 64 (sp + 12)) 4 = Some (Z_to_le_bytes 4 8) ->
  rdn SEGS m (Z_to_bv 64 (sp + 20)) 4 = Some (Z_to_le_bytes 4 w) ->
  getr regs 2 = Z_to_bv 64 sp ->
  getr regs 23 = Z_to_bv 64 (j + 1) ->
  getr regs 25 = Z_to_bv 64 w ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1c464) m rom) (@mkst fx regs' (Z_to_bv 64 0x1c468) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r []%list) regs regs'.
Proof using All.
  intros fx regs m  BT KC0 KC1 H2 H23 H25.
  dl_facts.
  ex_entry regs [sp; datag; datad; lineg; lined; w; j] HR.
  assert (HK : know_ok SEGS (ex_env regs [sp; datag; datad; lineg; lined; w; j]) m [KWord (SA (EVar 32) (12)) 4 (ELit 8); KWord (SA (EVar 32) (20)) 4 (EVar 37); KRange (EVar 32) 4096 140737488355328; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488355328; KAlign (EVar 36) 4; KRange (EVar 37) 1 20000; KRange (EVar 38) 0 19999]) by (ex_know regs).
  dl_run 400%nat [115620%Z; 115792%Z; 115816%Z] (SCR [false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma bp8_1c360t : forall (fx : FPState) regs m ,
  branch_taken BC_GE (Z_to_bv 64 (j + 1)) (Z_to_bv 64 w) = true ->
  rdn SEGS m (Z_to_bv 64 (sp + 12)) 4 = Some (Z_to_le_bytes 4 8) ->
  rdn SEGS m (Z_to_bv 64 (sp + 20)) 4 = Some (Z_to_le_bytes 4 w) ->
  getr regs 2 = Z_to_bv 64 sp ->
  getr regs 23 = Z_to_bv 64 (j + 1) ->
  getr regs 25 = Z_to_bv 64 w ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1c464) m rom) (@mkst fx regs' (Z_to_bv 64 0x1c3a4) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r []%list) regs regs'.
Proof using All.
  intros fx regs m  BT KC0 KC1 H2 H23 H25.
  dl_facts.
  ex_entry regs [sp; datag; datad; lineg; lined; w; j] HR.
  assert (HK : know_ok SEGS (ex_env regs [sp; datag; datad; lineg; lined; w; j]) m [KWord (SA (EVar 32) (12)) 4 (ELit 8); KWord (SA (EVar 32) (20)) 4 (EVar 37); KRange (EVar 32) 4096 140737488355328; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488355328; KAlign (EVar 36) 4; KRange (EVar 37) 1 20000; KRange (EVar 38) 0 19999]) by (ex_know regs).
  dl_run 400%nat [115620%Z; 115792%Z; 115816%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma bp8_1c364 : forall (fx : FPState) regs m (bs0 : list byte),
  rdn SEGS m (Z_to_bv 64 (bytea (lineg + j))) 1 = Some bs0 ->
  rdn SEGS m (Z_to_bv 64 (sp + 12)) 4 = Some (Z_to_le_bytes 4 8) ->
  rdn SEGS m (Z_to_bv 64 (sp + 20)) 4 = Some (Z_to_le_bytes 4 w) ->
  getr regs 2 = Z_to_bv 64 sp ->
  getr regs 5 = Z_to_bv 64 8 ->
  getr regs 6 = Z_to_bv 64 134217727 ->
  getr regs 7 = Z_to_bv 64 3 ->
  getr regs 8 = Z_to_bv 64 2 ->
  getr regs 9 = Z_to_bv 64 1 ->
  getr regs 11 = Z_to_bv 64 1 ->
  getr regs 14 = Z_to_bv 64 1 ->
  getr regs 15 = Z_to_bv 64 1 ->
  getr regs 16 = Z_to_bv 64 4 ->
  getr regs 18 = Z_to_bv 64 datag ->
  getr regs 20 = Z_to_bv 64 datad ->
  getr regs 23 = Z_to_bv 64 j ->
  getr regs 24 = Z_to_bv 64 lineg ->
  getr regs 28 = Z_to_bv 64 lineg ->
  getr regs 29 = Z_to_bv 64 lined ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1c468) m rom) (@mkst fx regs' (Z_to_bv 64 0x1c524) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r [25; 26]%list) regs regs'.
Proof using All.
  intros fx regs m bs0 R0 KC0 KC1 H2 H5 H6 H7 H8 H9 H11 H14 H15 H16 H18 H20 H23 H24 H28 H29.
  dl_facts.
  ex_entry regs [sp; datag; datad; lineg; lined; w; j; rdv false 1 bs0] HR.
  assert (HK : know_ok SEGS (ex_env regs [sp; datag; datad; lineg; lined; w; j; rdv false 1 bs0]) m [KWord (SA (EVar 32) (12)) 4 (ELit 8); KWord (SA (EVar 32) (20)) 4 (EVar 37); KRange (EVar 32) 4096 140737488355328; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488355328; KAlign (EVar 36) 4; KRange (EVar 37) 1 20000; KRange (EVar 38) 0 19999]) by (ex_know regs).
  dl_run 400%nat [115620%Z; 115792%Z; 115816%Z] (SCR [false] [EVar 39] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma bp8_1c420f : forall (fx : FPState) regs m (bs0 : list byte),
  branch_taken BC_NE (getr regs 25) (Z_to_bv 64 0) = false ->
  rdn SEGS m (Z_to_bv 64 (lined + (4 * (j / 32)))) 4 = Some bs0 ->
  store_ok SEGS m (Z_to_bv 64 (lined + (4 * (j / 32)))) 4 = true ->
  rdn SEGS m (Z_to_bv 64 (sp + 12)) 4 = Some (Z_to_le_bytes 4 8) ->
  rdn SEGS m (Z_to_bv 64 (sp + 20)) 4 = Some (Z_to_le_bytes 4 w) ->
  getr regs 2 = Z_to_bv 64 sp ->
  getr regs 5 = Z_to_bv 64 8 ->
  getr regs 6 = Z_to_bv 64 134217727 ->
  getr regs 7 = Z_to_bv 64 3 ->
  getr regs 8 = Z_to_bv 64 2 ->
  getr regs 9 = Z_to_bv 64 1 ->
  getr regs 11 = Z_to_bv 64 1 ->
  getr regs 14 = Z_to_bv 64 1 ->
  getr regs 15 = Z_to_bv 64 1 ->
  getr regs 16 = Z_to_bv 64 4 ->
  getr regs 18 = Z_to_bv 64 datag ->
  getr regs 20 = Z_to_bv 64 datad ->
  getr regs 23 = Z_to_bv 64 j ->
  getr regs 24 = Z_to_bv 64 lineg ->
  getr regs 28 = Z_to_bv 64 lineg ->
  getr regs 29 = Z_to_bv 64 lined ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1c524) m rom) (@mkst fx regs' (Z_to_bv 64 0x1c450) m' rom)
    /\ mframe [((lined + (4 * (j / 32)))%Z, 4%Z)] m m'
    /\ getr regs' 25 = Z_to_bv 64 (lined + (4 * (j / 32)))
    /\ regs_agree (fun r => In r [25; 26; 27]%list) regs regs'.
Proof using All.
  intros fx regs m bs0 BT R0 S0 KC0 KC1 H2 H5 H6 H7 H8 H9 H11 H14 H15 H16 H18 H20 H23 H24 H28 H29.
  dl_facts.
  ex_entry regs [sp; datag; datad; lineg; lined; w; j; rdv true 4 bs0] HR.
  assert (HK : know_ok SEGS (ex_env regs [sp; datag; datad; lineg; lined; w; j; rdv true 4 bs0]) m [KWord (SA (EVar 32) (12)) 4 (ELit 8); KWord (SA (EVar 32) (20)) 4 (EVar 37); KRange (EVar 32) 4096 140737488355328; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488355328; KAlign (EVar 36) 4; KRange (EVar 37) 1 20000; KRange (EVar 38) 0 19999]) by (ex_know regs).
  dl_run 400%nat [115620%Z; 115792%Z; 115816%Z] (SCR [false; false] [EVar 39] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma bp8_1c420t : forall (fx : FPState) regs m ,
  branch_taken BC_NE (getr regs 25) (Z_to_bv 64 0) = true ->
  rdn SEGS m (Z_to_bv 64 (sp + 12)) 4 = Some (Z_to_le_bytes 4 8) ->
  rdn SEGS m (Z_to_bv 64 (sp + 20)) 4 = Some (Z_to_le_bytes 4 w) ->
  getr regs 2 = Z_to_bv 64 sp ->
  getr regs 5 = Z_to_bv 64 8 ->
  getr regs 6 = Z_to_bv 64 134217727 ->
  getr regs 7 = Z_to_bv 64 3 ->
  getr regs 8 = Z_to_bv 64 2 ->
  getr regs 9 = Z_to_bv 64 1 ->
  getr regs 11 = Z_to_bv 64 1 ->
  getr regs 14 = Z_to_bv 64 1 ->
  getr regs 15 = Z_to_bv 64 1 ->
  getr regs 16 = Z_to_bv 64 4 ->
  getr regs 18 = Z_to_bv 64 datag ->
  getr regs 20 = Z_to_bv 64 datad ->
  getr regs 23 = Z_to_bv 64 j ->
  getr regs 24 = Z_to_bv 64 lineg ->
  getr regs 28 = Z_to_bv 64 lineg ->
  getr regs 29 = Z_to_bv 64 lined ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1c524) m rom) (@mkst fx regs' (Z_to_bv 64 0x1c450) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r []%list) regs regs'.
Proof using All.
  intros fx regs m  BT KC0 KC1 H2 H5 H6 H7 H8 H9 H11 H14 H15 H16 H18 H20 H23 H24 H28 H29.
  dl_facts.
  ex_entry regs [sp; datag; datad; lineg; lined; w; j] HR.
  assert (HK : know_ok SEGS (ex_env regs [sp; datag; datad; lineg; lined; w; j]) m [KWord (SA (EVar 32) (12)) 4 (ELit 8); KWord (SA (EVar 32) (20)) 4 (EVar 37); KRange (EVar 32) 4096 140737488355328; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488355328; KAlign (EVar 36) 4; KRange (EVar 37) 1 20000; KRange (EVar 38) 0 19999]) by (ex_know regs).
  dl_run 400%nat [115620%Z; 115792%Z; 115816%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Local Abbreviation bp8_1c364_cells := (bp8_1c364_cells_def sp datag datad lineg lined w j wplg wpld).
Local Abbreviation bp8_1c364_cells_w := (bp8_1c364_cells_w_def sp datag datad lineg lined w j wplg wpld).
Lemma bp8_1c364_path : forall (fx : FPState) regs m,
  cells_ok SEGS m bp8_1c364_cells ->
  (forall m', mframe bp8_1c364_cells_w m m' -> rdn SEGS m' (Z_to_bv 64 (sp + 12)) 4 = Some (Z_to_le_bytes 4 8)) ->
  (forall m', mframe bp8_1c364_cells_w m m' -> rdn SEGS m' (Z_to_bv 64 (sp + 20)) 4 = Some (Z_to_le_bytes 4 w)) ->
  getr regs 2 = Z_to_bv 64 sp ->
  getr regs 5 = Z_to_bv 64 8 ->
  getr regs 6 = Z_to_bv 64 134217727 ->
  getr regs 7 = Z_to_bv 64 3 ->
  getr regs 8 = Z_to_bv 64 2 ->
  getr regs 9 = Z_to_bv 64 1 ->
  getr regs 11 = Z_to_bv 64 1 ->
  getr regs 14 = Z_to_bv 64 1 ->
  getr regs 15 = Z_to_bv 64 1 ->
  getr regs 16 = Z_to_bv 64 4 ->
  getr regs 18 = Z_to_bv 64 datag ->
  getr regs 20 = Z_to_bv 64 datad ->
  getr regs 23 = Z_to_bv 64 j ->
  getr regs 24 = Z_to_bv 64 lineg ->
  getr regs 28 = Z_to_bv 64 lineg ->
  getr regs 29 = Z_to_bv 64 lined ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1c468) m rom) (@mkst fx regs' (Z_to_bv 64 0x1c450) m' rom)
    /\ mframe bp8_1c364_cells m m'
    /\ mframe bp8_1c364_cells_w m m'
    /\ regs_agree (fun r => In r [25; 26; 27]%list) regs regs'.
Proof using All.
  intros fx regs m CK  KCM0 KCM1 H2 H5 H6 H7 H8 H9 H11 H14 H15 H16 H18 H20 H23 H24 H28 H29.
  pose proof (mframe_refl bp8_1c364_cells m) as FK0.
  pose proof (mframe_refl bp8_1c364_cells_w m) as FW0.
  destruct (cells_ok_read SEGS m m bp8_1c364_cells (bytea (lineg + j))%Z 1%Z wr_readable_img CK (proj1 FK0) ltac:(dl_in0)) as [bs1_0 Rd1_0].
  destruct (bp8_1c364 fx regs m bs1_0 Rd1_0 (KCM0 m FW0) (KCM1 m FW0) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r1 & m1 & RUN1 & FR1 & AG1).
  assert (FK1 : mframe bp8_1c364_cells m m1) by (apply (mframe_step _ _ _ _ _ FK0 FR1); unfold bp8_1c364_cells_def; dl_incl).
  assert (FW1 : mframe bp8_1c364_cells_w m m1) by (apply (mframe_step _ _ _ _ _ FW0 FR1); unfold bp8_1c364_cells_w_def; dl_incl).
  destruct (branch_taken BC_NE (getr r1 25) (Z_to_bv 64 0)) eqn:B1.
  - (* [comment removed for export] *)
    destruct (bp8_1c420t fx r1 m1  B1 (KCM0 m1 FW1) (KCM1 m1 FW1) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r2 & m2 & RUN2 & FR2 & AG2).
    assert (FK2 : mframe bp8_1c364_cells m m2) by (apply (mframe_step _ _ _ _ _ FK1 FR2); unfold bp8_1c364_cells_def; dl_incl).
    assert (FW2 : mframe bp8_1c364_cells_w m m2) by (apply (mframe_step _ _ _ _ _ FW1 FR2); unfold bp8_1c364_cells_w_def; dl_incl).
    exists r2, m2. split; [exact (msteps_trans _ _ _ _ RUN1 RUN2)|]. split; [exact FK2|]. split; [exact FW2|].
    repeat split; [dl_get .. | ra_chain].
  - (* [comment removed for export] *)
    destruct (cells_ok_read SEGS m m1 bp8_1c364_cells (lined + (4 * (j / 32)))%Z 4%Z wr_readable_img CK (proj1 FK1) ltac:(dl_in0)) as [bs2_0 Rd2_0].
    destruct (bp8_1c420f fx r1 m1 bs2_0 B1 Rd2_0 (cells_ok_sok SEGS m m1 bp8_1c364_cells (lined + (4 * (j / 32)))%Z 4%Z CK (proj1 FK1) ltac:(dl_in0)) (KCM0 m1 FW1) (KCM1 m1 FW1) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r2 & m2 & RUN2 & FR2 & E2_25 & AG2).
    assert (FK2 : mframe bp8_1c364_cells m m2) by (apply (mframe_step _ _ _ _ _ FK1 FR2); unfold bp8_1c364_cells_def; dl_incl).
    assert (FW2 : mframe bp8_1c364_cells_w m m2) by (apply (mframe_step _ _ _ _ _ FW1 FR2); unfold bp8_1c364_cells_w_def; dl_incl).
    exists r2, m2. split; [exact (msteps_trans _ _ _ _ RUN1 RUN2)|]. split; [exact FK2|]. split; [exact FW2|].
    repeat split; [dl_get .. | ra_chain].
Qed.

End BP8.
