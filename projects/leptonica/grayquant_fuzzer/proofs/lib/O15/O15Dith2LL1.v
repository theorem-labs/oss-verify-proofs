(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.leptonica.grayquant_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare StoreOk StartupTac.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import WalksLib W2Lib LeptStructs LeptExec DitherLib DitherTac DitherLib2 DitherTac2 DitherTab.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require LiaFast.
Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Abbreviation SEGS := Plain.M.loaded_segments.

Lemma wr_readable_img : wr_readable SEGS.
Proof.
  intros seg Hin Hwr. cbn in Hin.
  repeat (destruct Hin as [<-|Hin]; [first [reflexivity | discriminate Hwr] |]). destruct Hin.
Qed.

Definition pc_1b380_cells_def (lined bufs1 bufs2 tabval tab38 w0 wpl wpld : Z) : list (Z * Z) := [((bytea (bufs1 + w0))%Z, 1%Z); ((lined + (4 * (w0 / 16)))%Z, 4%Z); ((bytea (bufs2 + w0))%Z, 1%Z)].
(* [comment removed for export] *)
Definition pc_hyps (lined bufs1 bufs2 tabval tab38 w0 wpl wpld : Z) : Prop :=
  (4096 <= lined <= 140737488355328)%Z /\ (lined mod 4 = 0)%Z /\ (4096 <= bufs1 <= 140737488355328)%Z /\ (bufs1 mod 4 = 0)%Z /\ (4096 <= bufs2 <= 140737488355328)%Z /\ (bufs2 mod 4 = 0)%Z /\ (4096 <= tabval <= 140737488355328)%Z /\ (tabval mod 4 = 0)%Z /\ (4096 <= tab38 <= 140737488355328)%Z /\ (tab38 mod 4 = 0)%Z /\ (0 <= w0 <= 19999)%Z /\ (w0 + 1 <= 4 * wpl)%Z /\ (w0 + 1 <= 16 * wpld)%Z /\ dapart lined (4 * wpld) bufs2 (4 * wpl) /\ dapart lined (4 * wpld) tab38 1024.
Section PC.
Variable rom : word -> option byte.
Variables (lined bufs1 bufs2 tabval tab38 w0 wpl wpld : Z).
Hypothesis HYP : pc_hyps lined bufs1 bufs2 tabval tab38 w0 wpl wpld.
Ltac dl_facts := pose proof HYP as (R_lined & A_lined & R_bufs1 & A_bufs1 & R_bufs2 & A_bufs2 & R_tabval & A_tabval & R_tab38 & A_tab38 & R_w0 & Hwpl & Hwpld & AP_l2 & AP_l38); pose proof (dl_div_bounds w0 16 ltac:(lia) ltac:(lia)) as DW; destruct (al4_ex _ A_bufs1) as [cb1 Ecb1]; destruct (al4_ex _ A_bufs2) as [cb2 Ecb2].
(* [comment removed for export] *)
Lemma pc_1b380 : forall (fx : FPState) regs m (bs0 : list byte) (bs1 : list byte) (bs2 : list byte) (bs3 : list byte) (bs4 : list byte),
  rdn SEGS m (Z_to_bv 64 (bytea (bufs1 + w0))) 1 = Some bs0 ->
  rdn SEGS m (Z_to_bv 64 (lined + (4 * (w0 / 16)))) 4 = Some bs1 ->
  rdn SEGS m (Z_to_bv 64 (tabval + (4 * (rdv false 1 bs0)))) 4 = Some bs2 ->
  rdn SEGS m (Z_to_bv 64 (bytea (bufs2 + w0))) 1 = Some bs3 ->
  rdn SEGS m (Z_to_bv 64 (tab38 + (4 * (rdv false 1 bs0)))) 4 = Some bs4 ->
  store_ok SEGS m (Z_to_bv 64 (lined + (4 * (w0 / 16)))) 4 = true ->
  getr regs 9 = Z_to_bv 64 bufs1 ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 w0 ->
  getr regs 18 = Z_to_bv 64 bufs2 ->
  getr regs 19 = Z_to_bv 64 tabval ->
  getr regs 20 = Z_to_bv 64 tab38 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b47c) m rom) (@mkst fx regs' (Z_to_bv 64 0x1b4e8) m' rom)
    /\ mframe [((lined + (4 * (w0 / 16)))%Z, 4%Z)] m m'
    /\ getr regs' 10 = Z_to_bv 64 (bytea (bufs2 + w0))
    /\ getr regs' 13 = Z_to_bv 64 (rdv true 4 bs4)
    /\ getr regs' 14 = Z_to_bv 64 255
    /\ getr regs' 16 = Z_to_bv 64 (rdv false 4 bs2)
    /\ regs_agree (fun r => In r [10; 11; 12; 13; 14; 15; 16]%list) regs regs'.
Proof using All.
  intros fx regs m bs0 bs1 bs2 bs3 bs4 R0 R1 R2 R3 R4 S0 H9 H10 H11 H18 H19 H20.
  dl_facts.
  pose proof (rdv_u8 SEGS _ _ _ R0) as U0.
  pose proof (rdv_u8 SEGS _ _ _ R3) as U3.
  ex_entry regs [lined; bufs1; bufs2; tabval; tab38; w0; rdv false 1 bs0; rdv true 4 bs1; rdv false 4 bs2; rdv false 1 bs3; rdv true 4 bs4] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; tabval; tab38; w0; rdv false 1 bs0; rdv true 4 bs1; rdv false 4 bs2; rdv false 1 bs3; rdv true 4 bs4]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488355328; KAlign (EVar 36) 4; KRange (EVar 37) 0 19999]) by (ex_know regs).
  dl_run 400%nat [111372%Z] (SCR [] [EVar 38; EVar 39; EVar 40; EVar 41; EVar 42] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma pc_1b3ecf : forall (fx : FPState) regs m ,
  branch_taken BC_LTU (getr regs 11) (Z_to_bv 64 255) = false ->
  getr regs 9 = Z_to_bv 64 bufs1 ->
  getr regs 10 = Z_to_bv 64 (bytea (bufs2 + w0)) ->
  getr regs 14 = Z_to_bv 64 255 ->
  getr regs 18 = Z_to_bv 64 bufs2 ->
  getr regs 19 = Z_to_bv 64 tabval ->
  getr regs 20 = Z_to_bv 64 tab38 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b4e8) m rom) (@mkst fx regs' (Z_to_bv 64 0x1b4f0) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 12 = Z_to_bv 64 255
    /\ regs_agree (fun r => In r [12]%list) regs regs'.
Proof using All.
  intros fx regs m  BT H9 H10 H14 H18 H19 H20.
  dl_facts.
  ex_entry regs [lined; bufs1; bufs2; tabval; tab38; w0] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; tabval; tab38; w0]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488355328; KAlign (EVar 36) 4; KRange (EVar 37) 0 19999]) by (ex_know regs).
  dl_run 400%nat [111372%Z] (SCR [false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma pc_1b3ect : forall (fx : FPState) regs m ,
  branch_taken BC_LTU (getr regs 11) (Z_to_bv 64 255) = true ->
  getr regs 9 = Z_to_bv 64 bufs1 ->
  getr regs 10 = Z_to_bv 64 (bytea (bufs2 + w0)) ->
  getr regs 14 = Z_to_bv 64 255 ->
  getr regs 18 = Z_to_bv 64 bufs2 ->
  getr regs 19 = Z_to_bv 64 tabval ->
  getr regs 20 = Z_to_bv 64 tab38 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b4e8) m rom) (@mkst fx regs' (Z_to_bv 64 0x1b4f0) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r []%list) regs regs'.
Proof using All.
  intros fx regs m  BT H9 H10 H14 H18 H19 H20.
  dl_facts.
  ex_entry regs [lined; bufs1; bufs2; tabval; tab38; w0] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; tabval; tab38; w0]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488355328; KAlign (EVar 36) 4; KRange (EVar 37) 0 19999]) by (ex_know regs).
  dl_run 400%nat [111372%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma pc_1b3f4f : forall (fx : FPState) regs m ,
  branch_taken BC_GE (getr regs 13) (Z_to_bv 64 0) = false ->
  store_ok SEGS m (Z_to_bv 64 (bytea (bufs2 + w0))) 1 = true ->
  getr regs 9 = Z_to_bv 64 bufs1 ->
  getr regs 10 = Z_to_bv 64 (bytea (bufs2 + w0)) ->
  getr regs 14 = Z_to_bv 64 255 ->
  getr regs 18 = Z_to_bv 64 bufs2 ->
  getr regs 19 = Z_to_bv 64 tabval ->
  getr regs 20 = Z_to_bv 64 tab38 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b4f0) m rom) (@mkst fx regs' (Z_to_bv 64 0x1b30c) m' rom)
    /\ mframe [((bytea (bufs2 + w0))%Z, 1%Z)] m m'
    /\ regs_agree (fun r => In r [12]%list) regs regs'.
Proof using All.
  intros fx regs m  BT S0 H9 H10 H14 H18 H19 H20.
  dl_facts.
  ex_entry regs [lined; bufs1; bufs2; tabval; tab38; w0] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; tabval; tab38; w0]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488355328; KAlign (EVar 36) 4; KRange (EVar 37) 0 19999]) by (ex_know regs).
  dl_run 400%nat [111372%Z] (SCR [false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma pc_1b3f4t : forall (fx : FPState) regs m ,
  branch_taken BC_GE (getr regs 13) (Z_to_bv 64 0) = true ->
  store_ok SEGS m (Z_to_bv 64 (bytea (bufs2 + w0))) 1 = true ->
  getr regs 9 = Z_to_bv 64 bufs1 ->
  getr regs 10 = Z_to_bv 64 (bytea (bufs2 + w0)) ->
  getr regs 14 = Z_to_bv 64 255 ->
  getr regs 18 = Z_to_bv 64 bufs2 ->
  getr regs 19 = Z_to_bv 64 tabval ->
  getr regs 20 = Z_to_bv 64 tab38 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b4f0) m rom) (@mkst fx regs' (Z_to_bv 64 0x1b30c) m' rom)
    /\ mframe [((bytea (bufs2 + w0))%Z, 1%Z)] m m'
    /\ regs_agree (fun r => In r []%list) regs regs'.
Proof using All.
  intros fx regs m  BT S0 H9 H10 H14 H18 H19 H20.
  dl_facts.
  ex_entry regs [lined; bufs1; bufs2; tabval; tab38; w0] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; tabval; tab38; w0]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488355328; KAlign (EVar 36) 4; KRange (EVar 37) 0 19999]) by (ex_know regs).
  dl_run 400%nat [111372%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Local Abbreviation pc_1b380_cells := (pc_1b380_cells_def lined bufs1 bufs2 tabval tab38 w0 wpl wpld).
Lemma pc_1b380_path : forall (fx : FPState) regs m,
  cells_ok SEGS m pc_1b380_cells ->
  tab_rd SEGS false (fun _ => True) pc_1b380_cells m tabval ->
  tab_rd SEGS true (fun _ => True) pc_1b380_cells m tab38 ->
  getr regs 9 = Z_to_bv 64 bufs1 ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 w0 ->
  getr regs 18 = Z_to_bv 64 bufs2 ->
  getr regs 19 = Z_to_bv 64 tabval ->
  getr regs 20 = Z_to_bv 64 tab38 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b47c) m rom) (@mkst fx regs' (Z_to_bv 64 0x1b30c) m' rom)
    /\ mframe pc_1b380_cells m m'
    /\ getr regs' 10 = Z_to_bv 64 (bytea (bufs2 + w0))
    /\ getr regs' 14 = Z_to_bv 64 255
    /\ regs_agree (fun r => In r [10; 11; 12; 13; 14; 15; 16]%list) regs regs'.
Proof using All.
  intros fx regs m CK TR_tabval_false TR_tab38_true H9 H10 H11 H18 H19 H20.
  pose proof (mframe_refl pc_1b380_cells m) as FK0.
  destruct (cells_ok_read SEGS m m pc_1b380_cells (bytea (bufs1 + w0))%Z 1%Z wr_readable_img CK (proj1 FK0) ltac:(dl_in0)) as [bs1_0 Rd1_0].
  destruct (cells_ok_read SEGS m m pc_1b380_cells (lined + (4 * (w0 / 16)))%Z 4%Z wr_readable_img CK (proj1 FK0) ltac:(dl_in0)) as [bs1_1 Rd1_1].
  destruct (TR_tabval_false m (rdv false 1 bs1_0)%Z FK0 ltac:(dl_u8)) as (bs1_2 & Rd1_2 & TV1_2).
  destruct (cells_ok_read SEGS m m pc_1b380_cells (bytea (bufs2 + w0))%Z 1%Z wr_readable_img CK (proj1 FK0) ltac:(dl_in0)) as [bs1_3 Rd1_3].
  destruct (TR_tab38_true m (rdv false 1 bs1_0)%Z FK0 ltac:(dl_u8)) as (bs1_4 & Rd1_4 & TV1_4).
  destruct (pc_1b380 fx regs m bs1_0 bs1_1 bs1_2 bs1_3 bs1_4 Rd1_0 Rd1_1 Rd1_2 Rd1_3 Rd1_4 (cells_ok_sok SEGS m m pc_1b380_cells (lined + (4 * (w0 / 16)))%Z 4%Z CK (proj1 FK0) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r1 & m1 & RUN1 & FR1 & E1_10 & E1_13 & E1_14 & E1_16 & AG1).
  assert (FK1 : mframe pc_1b380_cells m m1) by (apply (mframe_step _ _ _ _ _ FK0 FR1); unfold pc_1b380_cells_def; dl_incl).
  destruct (branch_taken BC_LTU (getr r1 11) (Z_to_bv 64 255)) eqn:B1.
  - (* [comment removed for export] *)
    destruct (pc_1b3ect fx r1 m1  B1 ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r2 & m2 & RUN2 & FR2 & AG2).
    assert (FK2 : mframe pc_1b380_cells m m2) by (apply (mframe_step _ _ _ _ _ FK1 FR2); unfold pc_1b380_cells_def; dl_incl).
    destruct (branch_taken BC_GE (getr r2 13) (Z_to_bv 64 0)) eqn:B2.
    + (* [comment removed for export] *)
      destruct (pc_1b3f4t fx r2 m2  B2 (cells_ok_sok SEGS m m2 pc_1b380_cells (bytea (bufs2 + w0))%Z 1%Z CK (proj1 FK2) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r3 & m3 & RUN3 & FR3 & AG3).
      assert (FK3 : mframe pc_1b380_cells m m3) by (apply (mframe_step _ _ _ _ _ FK2 FR3); unfold pc_1b380_cells_def; dl_incl).
      exists r3, m3. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 RUN3))|]. split; [exact FK3|].
      repeat split; [dl_get .. | ra_chain].
    + (* [comment removed for export] *)
      destruct (pc_1b3f4f fx r2 m2  B2 (cells_ok_sok SEGS m m2 pc_1b380_cells (bytea (bufs2 + w0))%Z 1%Z CK (proj1 FK2) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r3 & m3 & RUN3 & FR3 & AG3).
      assert (FK3 : mframe pc_1b380_cells m m3) by (apply (mframe_step _ _ _ _ _ FK2 FR3); unfold pc_1b380_cells_def; dl_incl).
      exists r3, m3. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 RUN3))|]. split; [exact FK3|].
      repeat split; [dl_get .. | ra_chain].
  - (* [comment removed for export] *)
    destruct (pc_1b3ecf fx r1 m1  B1 ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r2 & m2 & RUN2 & FR2 & E2_12 & AG2).
    assert (FK2 : mframe pc_1b380_cells m m2) by (apply (mframe_step _ _ _ _ _ FK1 FR2); unfold pc_1b380_cells_def; dl_incl).
    destruct (branch_taken BC_GE (getr r2 13) (Z_to_bv 64 0)) eqn:B2.
    + (* [comment removed for export] *)
      destruct (pc_1b3f4t fx r2 m2  B2 (cells_ok_sok SEGS m m2 pc_1b380_cells (bytea (bufs2 + w0))%Z 1%Z CK (proj1 FK2) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r3 & m3 & RUN3 & FR3 & AG3).
      assert (FK3 : mframe pc_1b380_cells m m3) by (apply (mframe_step _ _ _ _ _ FK2 FR3); unfold pc_1b380_cells_def; dl_incl).
      exists r3, m3. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 RUN3))|]. split; [exact FK3|].
      repeat split; [dl_get .. | ra_chain].
    + (* [comment removed for export] *)
      destruct (pc_1b3f4f fx r2 m2  B2 (cells_ok_sok SEGS m m2 pc_1b380_cells (bytea (bufs2 + w0))%Z 1%Z CK (proj1 FK2) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r3 & m3 & RUN3 & FR3 & AG3).
      assert (FK3 : mframe pc_1b380_cells m m3) by (apply (mframe_step _ _ _ _ _ FK2 FR3); unfold pc_1b380_cells_def; dl_incl).
      exists r3, m3. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 RUN3))|]. split; [exact FK3|].
      repeat split; [dl_get .. | ra_chain].
Qed.

End PC.

Definition pg_1b474_cells_def (lined bufs1 tabval tab38 j w1 wpl wpld : Z) : list (Z * Z) := [((bytea (bufs1 + j))%Z, 1%Z); ((lined + (4 * (j / 16)))%Z, 4%Z); ((bytea (bufs1 + j + 1))%Z, 1%Z)].
(* [comment removed for export] *)
Definition pg_hyps (lined bufs1 tabval tab38 j w1 wpl wpld : Z) : Prop :=
  (4096 <= lined <= 140737488355328)%Z /\ (lined mod 4 = 0)%Z /\ (4096 <= bufs1 <= 140737488355328)%Z /\ (bufs1 mod 4 = 0)%Z /\ (4096 <= tabval <= 140737488355328)%Z /\ (tabval mod 4 = 0)%Z /\ (4096 <= tab38 <= 140737488355328)%Z /\ (tab38 mod 4 = 0)%Z /\ (0 <= j <= 19999)%Z /\ (1 <= w1 <= 19999)%Z /\ (0 <= j < w1)%Z /\ (w1 + 1 <= 4 * wpl)%Z /\ (w1 + 1 <= 16 * wpld)%Z /\ dapart lined (4 * wpld) bufs1 (4 * wpl) /\ dapart lined (4 * wpld) tab38 1024.
Section PG.
Variable rom : word -> option byte.
Variables (lined bufs1 tabval tab38 j w1 wpl wpld : Z).
Hypothesis HYP : pg_hyps lined bufs1 tabval tab38 j w1 wpl wpld.
Ltac dl_facts := pose proof HYP as (R_lined & A_lined & R_bufs1 & A_bufs1 & R_tabval & A_tabval & R_tab38 & A_tab38 & R_j & R_w1 & Hj & Hwpl & Hwpld & AP_l1 & AP_l38); pose proof (dl_div_bounds j 16 ltac:(lia) ltac:(lia)) as DJ; destruct (al4_ex _ A_bufs1) as [cb1 Ecb1].
(* [comment removed for export] *)
Lemma pg_1b470f : forall (fx : FPState) regs m ,
  branch_taken BC_EQ (Z_to_bv 64 (j + 1)) (Z_to_bv 64 w1) = false ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 13 = Z_to_bv 64 (j + 1) ->
  getr regs 14 = Z_to_bv 64 w1 ->
  getr regs 16 = Z_to_bv 64 (bufs1 + j + 1) ->
  getr regs 19 = Z_to_bv 64 tabval ->
  getr regs 20 = Z_to_bv 64 tab38 ->
  getr regs 27 = Z_to_bv 64 268435455 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b56c) m rom) (@mkst fx regs' (Z_to_bv 64 0x1b570) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r []%list) regs regs'.
Proof using All.
  intros fx regs m  BT H10 H13 H14 H16 H19 H20 H27.
  dl_facts.
  ex_entry regs [lined; bufs1; tabval; tab38; j; w1; (bufs1 + j)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; tabval; tab38; j; w1; (bufs1 + j)%Z]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 0 19999; KRange (EVar 37) 1 19999; KRange (EVar 38) 4096 140737488375327]) by (ex_know regs).
  dl_run 400%nat [111980%Z; 111984%Z; 112128%Z] (SCR [false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma pg_1b470t : forall (fx : FPState) regs m ,
  branch_taken BC_EQ (Z_to_bv 64 (j + 1)) (Z_to_bv 64 w1) = true ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 13 = Z_to_bv 64 (j + 1) ->
  getr regs 14 = Z_to_bv 64 w1 ->
  getr regs 16 = Z_to_bv 64 (bufs1 + j + 1) ->
  getr regs 19 = Z_to_bv 64 tabval ->
  getr regs 20 = Z_to_bv 64 tab38 ->
  getr regs 27 = Z_to_bv 64 268435455 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b56c) m rom) (@mkst fx regs' (Z_to_bv 64 0x1b600) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r []%list) regs regs'.
Proof using All.
  intros fx regs m  BT H10 H13 H14 H16 H19 H20 H27.
  dl_facts.
  ex_entry regs [lined; bufs1; tabval; tab38; j; w1; (bufs1 + j)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; tabval; tab38; j; w1; (bufs1 + j)%Z]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 0 19999; KRange (EVar 37) 1 19999; KRange (EVar 38) 4096 140737488375327]) by (ex_know regs).
  dl_run 400%nat [111980%Z; 111984%Z; 112128%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma pg_1b474 : forall (fx : FPState) regs m (bs0 : list byte) (bs1 : list byte) (bs2 : list byte) (bs3 : list byte) (bs4 : list byte),
  rdn SEGS m (Z_to_bv 64 (bytea (bufs1 + j))) 1 = Some bs0 ->
  rdn SEGS m (Z_to_bv 64 (lined + (4 * (j / 16)))) 4 = Some bs1 ->
  rdn SEGS m (Z_to_bv 64 (tabval + (4 * (rdv false 1 bs0)))) 4 = Some bs2 ->
  rdn SEGS m (Z_to_bv 64 (bytea (bufs1 + j + 1))) 1 = Some bs3 ->
  rdn SEGS m (Z_to_bv 64 (tab38 + (4 * (rdv false 1 bs0)))) 4 = Some bs4 ->
  store_ok SEGS m (Z_to_bv 64 (lined + (4 * (j / 16)))) 4 = true ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 13 = Z_to_bv 64 j ->
  getr regs 14 = Z_to_bv 64 w1 ->
  getr regs 16 = Z_to_bv 64 (bufs1 + j) ->
  getr regs 19 = Z_to_bv 64 tabval ->
  getr regs 20 = Z_to_bv 64 tab38 ->
  getr regs 27 = Z_to_bv 64 268435455 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b570) m rom) (@mkst fx regs' (Z_to_bv 64 0x1b5dc) m' rom)
    /\ mframe [((lined + (4 * (j / 16)))%Z, 4%Z)] m m'
    /\ getr regs' 7 = Z_to_bv 64 (rdv true 4 bs4)
    /\ getr regs' 16 = Z_to_bv 64 (bufs1 + j + 1)
    /\ getr regs' 17 = Z_to_bv 64 (bytea (bufs1 + j + 1))
    /\ getr regs' 28 = Z_to_bv 64 255
    /\ regs_agree (fun r => In r [5; 6; 7; 16; 17; 28; 29]%list) regs regs'.
Proof using All.
  intros fx regs m bs0 bs1 bs2 bs3 bs4 R0 R1 R2 R3 R4 S0 H10 H13 H14 H16 H19 H20 H27.
  dl_facts.
  pose proof (rdv_u8 SEGS _ _ _ R0) as U0.
  pose proof (rdv_u8 SEGS _ _ _ R3) as U3.
  ex_entry regs [lined; bufs1; tabval; tab38; j; w1; (bufs1 + j)%Z; rdv false 1 bs0; rdv true 4 bs1; rdv false 4 bs2; rdv false 1 bs3; rdv true 4 bs4] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; tabval; tab38; j; w1; (bufs1 + j)%Z; rdv false 1 bs0; rdv true 4 bs1; rdv false 4 bs2; rdv false 1 bs3; rdv true 4 bs4]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 0 19999; KRange (EVar 37) 1 19999; KRange (EVar 38) 4096 140737488375327]) by (ex_know regs).
  dl_run 400%nat [111980%Z; 111984%Z; 112128%Z] (SCR [] [EVar 39; EVar 40; EVar 41; EVar 42; EVar 43] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma pg_1b4e0f : forall (fx : FPState) regs m ,
  branch_taken BC_LTU (getr regs 6) (Z_to_bv 64 255) = false ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 13 = Z_to_bv 64 j ->
  getr regs 14 = Z_to_bv 64 w1 ->
  getr regs 16 = Z_to_bv 64 (bufs1 + j + 1) ->
  getr regs 17 = Z_to_bv 64 (bytea (bufs1 + j + 1)) ->
  getr regs 19 = Z_to_bv 64 tabval ->
  getr regs 20 = Z_to_bv 64 tab38 ->
  getr regs 27 = Z_to_bv 64 268435455 ->
  getr regs 28 = Z_to_bv 64 255 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b5dc) m rom) (@mkst fx regs' (Z_to_bv 64 0x1b5e4) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 5 = Z_to_bv 64 255
    /\ regs_agree (fun r => In r [5]%list) regs regs'.
Proof using All.
  intros fx regs m  BT H10 H13 H14 H16 H17 H19 H20 H27 H28.
  dl_facts.
  ex_entry regs [lined; bufs1; tabval; tab38; j; w1; (bufs1 + j)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; tabval; tab38; j; w1; (bufs1 + j)%Z]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 0 19999; KRange (EVar 37) 1 19999; KRange (EVar 38) 4096 140737488375327]) by (ex_know regs).
  dl_run 400%nat [111980%Z; 111984%Z; 112128%Z] (SCR [false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma pg_1b4e0t : forall (fx : FPState) regs m ,
  branch_taken BC_LTU (getr regs 6) (Z_to_bv 64 255) = true ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 13 = Z_to_bv 64 j ->
  getr regs 14 = Z_to_bv 64 w1 ->
  getr regs 16 = Z_to_bv 64 (bufs1 + j + 1) ->
  getr regs 17 = Z_to_bv 64 (bytea (bufs1 + j + 1)) ->
  getr regs 19 = Z_to_bv 64 tabval ->
  getr regs 20 = Z_to_bv 64 tab38 ->
  getr regs 27 = Z_to_bv 64 268435455 ->
  getr regs 28 = Z_to_bv 64 255 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b5dc) m rom) (@mkst fx regs' (Z_to_bv 64 0x1b5e4) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r []%list) regs regs'.
Proof using All.
  intros fx regs m  BT H10 H13 H14 H16 H17 H19 H20 H27 H28.
  dl_facts.
  ex_entry regs [lined; bufs1; tabval; tab38; j; w1; (bufs1 + j)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; tabval; tab38; j; w1; (bufs1 + j)%Z]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 0 19999; KRange (EVar 37) 1 19999; KRange (EVar 38) 4096 140737488375327]) by (ex_know regs).
  dl_run 400%nat [111980%Z; 111984%Z; 112128%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma pg_1b4e8f : forall (fx : FPState) regs m ,
  branch_taken BC_GE (getr regs 7) (Z_to_bv 64 0) = false ->
  store_ok SEGS m (Z_to_bv 64 (bytea (bufs1 + j + 1))) 1 = true ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 13 = Z_to_bv 64 j ->
  getr regs 14 = Z_to_bv 64 w1 ->
  getr regs 16 = Z_to_bv 64 (bufs1 + j + 1) ->
  getr regs 17 = Z_to_bv 64 (bytea (bufs1 + j + 1)) ->
  getr regs 19 = Z_to_bv 64 tabval ->
  getr regs 20 = Z_to_bv 64 tab38 ->
  getr regs 27 = Z_to_bv 64 268435455 ->
  getr regs 28 = Z_to_bv 64 255 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b5e4) m rom) (@mkst fx regs' (Z_to_bv 64 0x1b56c) m' rom)
    /\ mframe [((bytea (bufs1 + j + 1))%Z, 1%Z)] m m'
    /\ getr regs' 13 = Z_to_bv 64 (j + 1)
    /\ regs_agree (fun r => In r [5; 12; 13]%list) regs regs'.
Proof using All.
  intros fx regs m  BT S0 H10 H13 H14 H16 H17 H19 H20 H27 H28.
  dl_facts.
  ex_entry regs [lined; bufs1; tabval; tab38; j; w1; (bufs1 + j)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; tabval; tab38; j; w1; (bufs1 + j)%Z]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 0 19999; KRange (EVar 37) 1 19999; KRange (EVar 38) 4096 140737488375327]) by (ex_know regs).
  dl_run 400%nat [111980%Z; 111984%Z; 112128%Z] (SCR [false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma pg_1b4e8t : forall (fx : FPState) regs m ,
  branch_taken BC_GE (getr regs 7) (Z_to_bv 64 0) = true ->
  store_ok SEGS m (Z_to_bv 64 (bytea (bufs1 + j + 1))) 1 = true ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 13 = Z_to_bv 64 j ->
  getr regs 14 = Z_to_bv 64 w1 ->
  getr regs 16 = Z_to_bv 64 (bufs1 + j + 1) ->
  getr regs 17 = Z_to_bv 64 (bytea (bufs1 + j + 1)) ->
  getr regs 19 = Z_to_bv 64 tabval ->
  getr regs 20 = Z_to_bv 64 tab38 ->
  getr regs 27 = Z_to_bv 64 268435455 ->
  getr regs 28 = Z_to_bv 64 255 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b5e4) m rom) (@mkst fx regs' (Z_to_bv 64 0x1b56c) m' rom)
    /\ mframe [((bytea (bufs1 + j + 1))%Z, 1%Z)] m m'
    /\ getr regs' 13 = Z_to_bv 64 (j + 1)
    /\ regs_agree (fun r => In r [12; 13]%list) regs regs'.
Proof using All.
  intros fx regs m  BT S0 H10 H13 H14 H16 H17 H19 H20 H27 H28.
  dl_facts.
  ex_entry regs [lined; bufs1; tabval; tab38; j; w1; (bufs1 + j)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; tabval; tab38; j; w1; (bufs1 + j)%Z]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 0 19999; KRange (EVar 37) 1 19999; KRange (EVar 38) 4096 140737488375327]) by (ex_know regs).
  dl_run 400%nat [111980%Z; 111984%Z; 112128%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Local Abbreviation pg_1b474_cells := (pg_1b474_cells_def lined bufs1 tabval tab38 j w1 wpl wpld).
Lemma pg_1b474_path : forall (fx : FPState) regs m,
  cells_ok SEGS m pg_1b474_cells ->
  tab_rd SEGS false (fun _ => True) pg_1b474_cells m tabval ->
  tab_rd SEGS true (fun _ => True) pg_1b474_cells m tab38 ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 13 = Z_to_bv 64 j ->
  getr regs 14 = Z_to_bv 64 w1 ->
  getr regs 16 = Z_to_bv 64 (bufs1 + j) ->
  getr regs 19 = Z_to_bv 64 tabval ->
  getr regs 20 = Z_to_bv 64 tab38 ->
  getr regs 27 = Z_to_bv 64 268435455 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b570) m rom) (@mkst fx regs' (Z_to_bv 64 0x1b56c) m' rom)
    /\ mframe pg_1b474_cells m m'
    /\ getr regs' 13 = Z_to_bv 64 (j + 1)
    /\ getr regs' 16 = Z_to_bv 64 (bufs1 + j + 1)
    /\ getr regs' 17 = Z_to_bv 64 (bytea (bufs1 + j + 1))
    /\ getr regs' 28 = Z_to_bv 64 255
    /\ regs_agree (fun r => In r [5; 6; 7; 12; 13; 16; 17; 28; 29]%list) regs regs'.
Proof using All.
  intros fx regs m CK TR_tabval_false TR_tab38_true H10 H13 H14 H16 H19 H20 H27.
  pose proof (mframe_refl pg_1b474_cells m) as FK0.
  destruct (cells_ok_read SEGS m m pg_1b474_cells (bytea (bufs1 + j))%Z 1%Z wr_readable_img CK (proj1 FK0) ltac:(dl_in0)) as [bs1_0 Rd1_0].
  destruct (cells_ok_read SEGS m m pg_1b474_cells (lined + (4 * (j / 16)))%Z 4%Z wr_readable_img CK (proj1 FK0) ltac:(dl_in0)) as [bs1_1 Rd1_1].
  destruct (TR_tabval_false m (rdv false 1 bs1_0)%Z FK0 ltac:(dl_u8)) as (bs1_2 & Rd1_2 & TV1_2).
  destruct (cells_ok_read SEGS m m pg_1b474_cells (bytea (bufs1 + j + 1))%Z 1%Z wr_readable_img CK (proj1 FK0) ltac:(dl_in0)) as [bs1_3 Rd1_3].
  destruct (TR_tab38_true m (rdv false 1 bs1_0)%Z FK0 ltac:(dl_u8)) as (bs1_4 & Rd1_4 & TV1_4).
  destruct (pg_1b474 fx regs m bs1_0 bs1_1 bs1_2 bs1_3 bs1_4 Rd1_0 Rd1_1 Rd1_2 Rd1_3 Rd1_4 (cells_ok_sok SEGS m m pg_1b474_cells (lined + (4 * (j / 16)))%Z 4%Z CK (proj1 FK0) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r1 & m1 & RUN1 & FR1 & E1_7 & E1_16 & E1_17 & E1_28 & AG1).
  assert (FK1 : mframe pg_1b474_cells m m1) by (apply (mframe_step _ _ _ _ _ FK0 FR1); unfold pg_1b474_cells_def; dl_incl).
  destruct (branch_taken BC_LTU (getr r1 6) (Z_to_bv 64 255)) eqn:B1.
  - (* [comment removed for export] *)
    destruct (pg_1b4e0t fx r1 m1  B1 ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r2 & m2 & RUN2 & FR2 & AG2).
    assert (FK2 : mframe pg_1b474_cells m m2) by (apply (mframe_step _ _ _ _ _ FK1 FR2); unfold pg_1b474_cells_def; dl_incl).
    destruct (branch_taken BC_GE (getr r2 7) (Z_to_bv 64 0)) eqn:B2.
    + (* [comment removed for export] *)
      destruct (pg_1b4e8t fx r2 m2  B2 (cells_ok_sok SEGS m m2 pg_1b474_cells (bytea (bufs1 + j + 1))%Z 1%Z CK (proj1 FK2) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r3 & m3 & RUN3 & FR3 & E3_13 & AG3).
      assert (FK3 : mframe pg_1b474_cells m m3) by (apply (mframe_step _ _ _ _ _ FK2 FR3); unfold pg_1b474_cells_def; dl_incl).
      exists r3, m3. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 RUN3))|]. split; [exact FK3|].
      repeat split; [dl_get .. | ra_chain].
    + (* [comment removed for export] *)
      destruct (pg_1b4e8f fx r2 m2  B2 (cells_ok_sok SEGS m m2 pg_1b474_cells (bytea (bufs1 + j + 1))%Z 1%Z CK (proj1 FK2) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r3 & m3 & RUN3 & FR3 & E3_13 & AG3).
      assert (FK3 : mframe pg_1b474_cells m m3) by (apply (mframe_step _ _ _ _ _ FK2 FR3); unfold pg_1b474_cells_def; dl_incl).
      exists r3, m3. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 RUN3))|]. split; [exact FK3|].
      repeat split; [dl_get .. | ra_chain].
  - (* [comment removed for export] *)
    destruct (pg_1b4e0f fx r1 m1  B1 ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r2 & m2 & RUN2 & FR2 & E2_5 & AG2).
    assert (FK2 : mframe pg_1b474_cells m m2) by (apply (mframe_step _ _ _ _ _ FK1 FR2); unfold pg_1b474_cells_def; dl_incl).
    destruct (branch_taken BC_GE (getr r2 7) (Z_to_bv 64 0)) eqn:B2.
    + (* [comment removed for export] *)
      destruct (pg_1b4e8t fx r2 m2  B2 (cells_ok_sok SEGS m m2 pg_1b474_cells (bytea (bufs1 + j + 1))%Z 1%Z CK (proj1 FK2) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r3 & m3 & RUN3 & FR3 & E3_13 & AG3).
      assert (FK3 : mframe pg_1b474_cells m m3) by (apply (mframe_step _ _ _ _ _ FK2 FR3); unfold pg_1b474_cells_def; dl_incl).
      exists r3, m3. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 RUN3))|]. split; [exact FK3|].
      repeat split; [dl_get .. | ra_chain].
    + (* [comment removed for export] *)
      destruct (pg_1b4e8f fx r2 m2  B2 (cells_ok_sok SEGS m m2 pg_1b474_cells (bytea (bufs1 + j + 1))%Z 1%Z CK (proj1 FK2) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r3 & m3 & RUN3 & FR3 & E3_13 & AG3).
      assert (FK3 : mframe pg_1b474_cells m m3) by (apply (mframe_step _ _ _ _ _ FK2 FR3); unfold pg_1b474_cells_def; dl_incl).
      exists r3, m3. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 RUN3))|]. split; [exact FK3|].
      repeat split; [dl_get .. | ra_chain].
Qed.

End PG.

Definition pl_1b504_cells_def (lined bufs1 tabval w0 wpl wpld : Z) : list (Z * Z) := [((bytea (bufs1 + w0))%Z, 1%Z); ((lined + (4 * (w0 / 16)))%Z, 4%Z)].
(* [comment removed for export] *)
Definition pl_hyps (lined bufs1 tabval w0 wpl wpld : Z) : Prop :=
  (4096 <= lined <= 140737488355328)%Z /\ (lined mod 4 = 0)%Z /\ (4096 <= bufs1 <= 140737488355328)%Z /\ (bufs1 mod 4 = 0)%Z /\ (4096 <= tabval <= 140737488355328)%Z /\ (tabval mod 4 = 0)%Z /\ (0 <= w0 <= 19999)%Z /\ (w0 + 1 <= 4 * wpl)%Z /\ (w0 + 1 <= 16 * wpld)%Z.
Section PL.
Variable rom : word -> option byte.
Variables (lined bufs1 tabval w0 wpl wpld : Z).
Hypothesis HYP : pl_hyps lined bufs1 tabval w0 wpl wpld.
Ltac dl_facts := pose proof HYP as (R_lined & A_lined & R_bufs1 & A_bufs1 & R_tabval & A_tabval & R_w0 & Hwpl & Hwpld); pose proof (dl_div_bounds w0 16 ltac:(lia) ltac:(lia)) as DW; destruct (al4_ex _ A_bufs1) as [cb1 Ecb1].
(* [comment removed for export] *)
Lemma pl_1b504 : forall (fx : FPState) regs m (bs0 : list byte) (bs1 : list byte) (bs2 : list byte),
  rdn SEGS m (Z_to_bv 64 (bytea (bufs1 + w0))) 1 = Some bs0 ->
  rdn SEGS m (Z_to_bv 64 (lined + (4 * (w0 / 16)))) 4 = Some bs1 ->
  rdn SEGS m (Z_to_bv 64 (tabval + (4 * (rdv false 1 bs0)))) 4 = Some bs2 ->
  store_ok SEGS m (Z_to_bv 64 (lined + (4 * (w0 / 16)))) 4 = true ->
  getr regs 8 = Z_to_bv 64 w0 ->
  getr regs 9 = Z_to_bv 64 bufs1 ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 19 = Z_to_bv 64 tabval ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b600) m rom) (@mkst fx regs' (Z_to_bv 64 0x1b650) m' rom)
    /\ mframe [((lined + (4 * (w0 / 16)))%Z, 4%Z)] m m'
    /\ getr regs' 10 = Z_to_bv 64 (lined + (4 * (w0 / 16)))
    /\ regs_agree (fun r => In r [10; 12; 13; 14; 15]%list) regs regs'.
Proof using All.
  intros fx regs m bs0 bs1 bs2 R0 R1 R2 S0 H8 H9 H10 H19.
  dl_facts.
  pose proof (rdv_u8 SEGS _ _ _ R0) as U0.
  ex_entry regs [lined; bufs1; tabval; w0; rdv false 1 bs0; rdv true 4 bs1; rdv false 4 bs2] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; tabval; w0; rdv false 1 bs0; rdv true 4 bs1; rdv false 4 bs2]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 19999]) by (ex_know regs).
  dl_run 400%nat [112208%Z] (SCR [] [EVar 36; EVar 37; EVar 38] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Local Abbreviation pl_1b504_cells := (pl_1b504_cells_def lined bufs1 tabval w0 wpl wpld).
Lemma pl_1b504_path : forall (fx : FPState) regs m,
  cells_ok SEGS m pl_1b504_cells ->
  tab_rd SEGS false (fun _ => True) pl_1b504_cells m tabval ->
  getr regs 8 = Z_to_bv 64 w0 ->
  getr regs 9 = Z_to_bv 64 bufs1 ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 19 = Z_to_bv 64 tabval ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b600) m rom) (@mkst fx regs' (Z_to_bv 64 0x1b650) m' rom)
    /\ mframe pl_1b504_cells m m'
    /\ getr regs' 10 = Z_to_bv 64 (lined + (4 * (w0 / 16)))
    /\ regs_agree (fun r => In r [10; 12; 13; 14; 15]%list) regs regs'.
Proof using All.
  intros fx regs m CK TR_tabval_false H8 H9 H10 H19.
  pose proof (mframe_refl pl_1b504_cells m) as FK0.
  destruct (cells_ok_read SEGS m m pl_1b504_cells (bytea (bufs1 + w0))%Z 1%Z wr_readable_img CK (proj1 FK0) ltac:(dl_in0)) as [bs1_0 Rd1_0].
  destruct (cells_ok_read SEGS m m pl_1b504_cells (lined + (4 * (w0 / 16)))%Z 4%Z wr_readable_img CK (proj1 FK0) ltac:(dl_in0)) as [bs1_1 Rd1_1].
  destruct (TR_tabval_false m (rdv false 1 bs1_0)%Z FK0 ltac:(dl_u8)) as (bs1_2 & Rd1_2 & TV1_2).
  destruct (pl_1b504 fx regs m bs1_0 bs1_1 bs1_2 Rd1_0 Rd1_1 Rd1_2 (cells_ok_sok SEGS m m pl_1b504_cells (lined + (4 * (w0 / 16)))%Z 4%Z CK (proj1 FK0) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r1 & m1 & RUN1 & FR1 & E1_10 & AG1).
  assert (FK1 : mframe pl_1b504_cells m m1) by (apply (mframe_step _ _ _ _ _ FK0 FR1); unfold pl_1b504_cells_def; dl_incl).
  exists r1, m1. split; [exact RUN1|]. split; [exact FK1|].
  repeat split; [dl_get .. | ra_chain].
Qed.

End PL.
