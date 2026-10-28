(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.grayquant_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare StoreOk StartupTac.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import WalksLib W2Lib LeptStructs LeptExec DitherLib DitherTac DitherLib2 DitherTac2 DitherTab DitherTabW.
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

(* [comment removed for export] *)
Definition wa_hyps (sp datad datat h : Z) : Prop :=
  (4096 <= sp <= 140737488355328)%Z /\ (4096 <= datad <= 140737488355328)%Z /\ (datad mod 4 = 0)%Z /\ (4096 <= datat <= 140737488355328)%Z /\ (datat mod 4 = 0)%Z /\ (1 <= h <= 20000)%Z.
Section WA.
Variable rom : word -> option byte.
Variables (sp datad datat h : Z).
Hypothesis HYP : wa_hyps sp datad datat h.
Ltac dl_facts := pose proof HYP as (R_sp & R_datad & A_datad & R_datat & A_datat & R_h); idtac.
(* [comment removed for export] *)
Lemma wa_1dbac : forall (fx : FPState) regs m ,
  getr regs 2 = Z_to_bv 64 sp ->
  getr regs 9 = Z_to_bv 64 datat ->
  getr regs 11 = Z_to_bv 64 h ->
  getr regs 18 = Z_to_bv 64 datad ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1dcb0) m rom) (@mkst fx regs' (Z_to_bv 64 0x1dce4) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 10 = Z_to_bv 64 0
    /\ getr regs' 11 = Z_to_bv 64 0
    /\ getr regs' 12 = Z_to_bv 64 0
    /\ getr regs' 13 = Z_to_bv 64 1
    /\ getr regs' 15 = Z_to_bv 64 1
    /\ getr regs' 16 = Z_to_bv 64 3
    /\ regs_agree (fun r => In r [10; 11; 12; 13; 15; 16]%list) regs regs'.
Proof using All.
  intros fx regs m  H2 H9 H11 H18.
  dl_facts.
  ex_entry regs [sp; datad; datat; h] HR.
  assert (HK : know_ok SEGS (ex_env regs [sp; datad; datat; h]) m [KRange (EVar 32) 4096 140737488355328; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 1 20000]) by (ex_know regs).
  dl_run 400%nat [122084%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

End WA.

(* [comment removed for export] *)
Definition wr_hyps (sp datad datat w h wpld wplt i accd acct : Z) : Prop :=
  (4096 <= sp <= 140737488355328)%Z /\ (4096 <= datad <= 140737488355328)%Z /\ (datad mod 4 = 0)%Z /\ (4096 <= datat <= 140737488355328)%Z /\ (datat mod 4 = 0)%Z /\ (1 <= w <= 20000)%Z /\ (1 <= h <= 20000)%Z /\ (1 <= wpld <= 5000)%Z /\ (1 <= wplt <= 5000)%Z /\ (0 <= i <= 19999)%Z /\ (0 <= accd <= 67108864)%Z /\ (0 <= acct <= 67108864)%Z /\ (accd = i * wpld)%Z /\ (acct = i * wplt)%Z /\ (0 <= i * wpld < 2 ^ 26)%Z /\ (0 <= i * wplt < 2 ^ 26)%Z.
Section WR.
Variable rom : word -> option byte.
Variables (sp datad datat w h wpld wplt i accd acct : Z).
Hypothesis HYP : wr_hyps sp datad datat w h wpld wplt i accd acct.
Ltac dl_facts := pose proof HYP as (R_sp & R_datad & A_datad & R_datat & A_datat & R_w & R_h & R_wpld & R_wplt & R_i & R_accd & R_acct & Ead & Eat & Hpd & Hpt); idtac.
(* [comment removed for export] *)
Lemma wr_1dbe0 : forall (fx : FPState) regs m ,
  rdn SEGS m (Z_to_bv 64 (sp + 84)) 4 = Some (Z_to_le_bytes 4 w) ->
  getr regs 2 = Z_to_bv 64 sp ->
  getr regs 9 = Z_to_bv 64 datat ->
  getr regs 10 = Z_to_bv 64 accd ->
  getr regs 11 = Z_to_bv 64 acct ->
  getr regs 12 = Z_to_bv 64 i ->
  getr regs 13 = Z_to_bv 64 1 ->
  getr regs 14 = Z_to_bv 64 wplt ->
  getr regs 15 = Z_to_bv 64 1 ->
  getr regs 16 = Z_to_bv 64 3 ->
  getr regs 18 = Z_to_bv 64 datad ->
  getr regs 19 = Z_to_bv 64 wpld ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1dce4) m rom) (@mkst fx regs' (Z_to_bv 64 0x1dd70) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 5 = Z_to_bv 64 (datat + (4 * (i * wplt)))
    /\ getr regs' 6 = Z_to_bv 64 0
    /\ getr regs' 7 = Z_to_bv 64 (datat + (4 * acct))
    /\ getr regs' 17 = Z_to_bv 64 (datad + (4 * (i * wpld)))
    /\ getr regs' 28 = Z_to_bv 64 (datad + (4 * accd))
    /\ getr regs' 29 = Z_to_bv 64 (datad + (4 * accd))
    /\ getr regs' 30 = Z_to_bv 64 (datat + (4 * acct))
    /\ regs_agree (fun r => In r [5; 6; 7; 17; 28; 29; 30]%list) regs regs'.
Proof using All.
  intros fx regs m  KC0 H2 H9 H10 H11 H12 H13 H14 H15 H16 H18 H19.
  dl_facts.
  ex_entry regs [sp; datad; datat; w; h; wpld; wplt; i; accd; acct] HR.
  assert (HK : know_ok SEGS (ex_env regs [sp; datad; datat; w; h; wpld; wplt; i; accd; acct]) m [KWord (SA (EVar 32) (84)) 4 (EVar 35); KRange (EVar 32) 4096 140737488355328; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 1 20000; KRange (EVar 36) 1 20000; KRange (EVar 37) 1 5000; KRange (EVar 38) 1 5000; KRange (EVar 39) 0 19999; KRange (EVar 40) 0 67108864; KRange (EVar 41) 0 67108864]) by (ex_know regs).
  dl_run 400%nat [122224%Z] (SCR [false; false; false; false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

End WR.

Definition wp_1dc6c_cells_def (sp drow srow qtab w j wpld wplt : Z) : list (Z * Z) := [((bytea (srow + j))%Z, 1%Z); ((bytea (drow + j))%Z, 1%Z)].
Definition wp_1dc6c_cells_w_def (sp drow srow qtab w j wpld wplt : Z) : list (Z * Z) := [((bytea (drow + j))%Z, 1%Z)].
(* [comment removed for export] *)
Definition wp_hyps (sp drow srow qtab w j wpld wplt : Z) : Prop :=
  (4096 <= sp <= 140737488355328)%Z /\ (4096 <= drow <= 140737488355328)%Z /\ (drow mod 4 = 0)%Z /\ (4096 <= srow <= 140737488355328)%Z /\ (srow mod 4 = 0)%Z /\ (4096 <= qtab <= 140737488355328)%Z /\ (qtab mod 4 = 0)%Z /\ (1 <= w <= 20000)%Z /\ (0 <= j <= 19999)%Z /\ (0 <= j < w)%Z /\ (w <= 4 * wpld)%Z /\ (w <= 4 * wplt)%Z /\ dapart drow (4 * wpld) sp 96.
Section WP.
Variable rom : word -> option byte.
Variables (sp drow srow qtab w j wpld wplt : Z).
Hypothesis HYP : wp_hyps sp drow srow qtab w j wpld wplt.
Ltac dl_facts := pose proof HYP as (R_sp & R_drow & A_drow & R_srow & A_srow & R_qtab & A_qtab & R_w & R_j & Hj & Hwd & Hwt & AP_df); destruct (al4_ex _ A_drow) as [cd Ecd]; destruct (al4_ex _ A_srow) as [cs Ecs].
(* [comment removed for export] *)
Lemma wp_1dc6c : forall (fx : FPState) regs m (bs0 : list byte) (bs1 : list byte),
  rdn SEGS m (Z_to_bv 64 (bytea (srow + j))) 1 = Some bs0 ->
  rdn SEGS m (Z_to_bv 64 (qtab + (4 * (rdv false 1 bs0)))) 4 = Some bs1 ->
  store_ok SEGS m (Z_to_bv 64 (bytea (drow + j))) 1 = true ->
  rdn SEGS m (Z_to_bv 64 (sp + 84)) 4 = Some (Z_to_le_bytes 4 w) ->
  rdn SEGS m (Z_to_bv 64 (sp + 88)) 8 = Some (Z_to_le_bytes 8 qtab) ->
  getr regs 2 = Z_to_bv 64 sp ->
  getr regs 5 = Z_to_bv 64 srow ->
  getr regs 6 = Z_to_bv 64 j ->
  getr regs 7 = Z_to_bv 64 (srow + j) ->
  getr regs 13 = Z_to_bv 64 1 ->
  getr regs 15 = Z_to_bv 64 1 ->
  getr regs 16 = Z_to_bv 64 3 ->
  getr regs 17 = Z_to_bv 64 drow ->
  getr regs 28 = Z_to_bv 64 (drow + j) ->
  getr regs 29 = Z_to_bv 64 (drow + j) ->
  getr regs 30 = Z_to_bv 64 (srow + j) ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1dd70) m rom) (@mkst fx regs' (Z_to_bv 64 0x1ddf0) m' rom)
    /\ mframe [((bytea (drow + j))%Z, 1%Z)] m m'
    /\ getr regs' 6 = Z_to_bv 64 (j + 1)
    /\ getr regs' 7 = Z_to_bv 64 (srow + j + 1)
    /\ getr regs' 8 = Z_to_bv 64 (bytea (drow + j))
    /\ getr regs' 22 = Z_to_bv 64 0
    /\ getr regs' 28 = Z_to_bv 64 (drow + j + 1)
    /\ getr regs' 29 = Z_to_bv 64 (drow + j + 1)
    /\ getr regs' 30 = Z_to_bv 64 (srow + j + 1)
    /\ getr regs' 31 = Z_to_bv 64 w
    /\ regs_agree (fun r => In r [6; 7; 8; 20; 22; 28; 29; 30; 31]%list) regs regs'.
Proof using All.
  intros fx regs m bs0 bs1 R0 R1 S0 KC0 KC1 H2 H5 H6 H7 H13 H15 H16 H17 H28 H29 H30.
  dl_facts.
  pose proof (rdv_u8 SEGS _ _ _ R0) as U0.
  ex_entry regs [sp; drow; srow; qtab; w; j; (srow + j)%Z; (drow + j)%Z; rdv false 1 bs0; rdv true 4 bs1] HR.
  assert (HK : know_ok SEGS (ex_env regs [sp; drow; srow; qtab; w; j; (srow + j)%Z; (drow + j)%Z; rdv false 1 bs0; rdv true 4 bs1]) m [KWord (SA (EVar 32) (84)) 4 (EVar 36); KWord (SA (EVar 32) (88)) 8 (EVar 35); KRange (EVar 32) 4096 140737488355328; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 1 20000; KRange (EVar 37) 0 19999; KRange (EVar 38) 4096 140737488375327; KRange (EVar 39) 4096 140737488375327]) by (ex_know regs).
  dl_run 400%nat [122064%Z; 122224%Z; 122352%Z] (SCR [false; false; false; false] [EVar 40; EVar 41] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma wp_1dcecf : forall (fx : FPState) regs m ,
  branch_taken BC_LT (Z_to_bv 64 (j + 1)) (Z_to_bv 64 w) = false ->
  rdn SEGS m (Z_to_bv 64 (sp + 84)) 4 = Some (Z_to_le_bytes 4 w) ->
  rdn SEGS m (Z_to_bv 64 (sp + 88)) 8 = Some (Z_to_le_bytes 8 qtab) ->
  getr regs 2 = Z_to_bv 64 sp ->
  getr regs 5 = Z_to_bv 64 srow ->
  getr regs 6 = Z_to_bv 64 (j + 1) ->
  getr regs 7 = Z_to_bv 64 (srow + j + 1) ->
  getr regs 13 = Z_to_bv 64 1 ->
  getr regs 15 = Z_to_bv 64 1 ->
  getr regs 16 = Z_to_bv 64 3 ->
  getr regs 17 = Z_to_bv 64 drow ->
  getr regs 28 = Z_to_bv 64 (drow + j + 1) ->
  getr regs 29 = Z_to_bv 64 (drow + j + 1) ->
  getr regs 30 = Z_to_bv 64 (srow + j + 1) ->
  getr regs 31 = Z_to_bv 64 w ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1ddf0) m rom) (@mkst fx regs' (Z_to_bv 64 0x1dcd0) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r []%list) regs regs'.
Proof using All.
  intros fx regs m  BT KC0 KC1 H2 H5 H6 H7 H13 H15 H16 H17 H28 H29 H30 H31.
  dl_facts.
  ex_entry regs [sp; drow; srow; qtab; w; j; (srow + j)%Z; (drow + j)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [sp; drow; srow; qtab; w; j; (srow + j)%Z; (drow + j)%Z]) m [KWord (SA (EVar 32) (84)) 4 (EVar 36); KWord (SA (EVar 32) (88)) 8 (EVar 35); KRange (EVar 32) 4096 140737488355328; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 1 20000; KRange (EVar 37) 0 19999; KRange (EVar 38) 4096 140737488375327; KRange (EVar 39) 4096 140737488375327]) by (ex_know regs).
  dl_run 400%nat [122064%Z; 122224%Z; 122352%Z] (SCR [false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma wp_1dcect : forall (fx : FPState) regs m ,
  branch_taken BC_LT (Z_to_bv 64 (j + 1)) (Z_to_bv 64 w) = true ->
  rdn SEGS m (Z_to_bv 64 (sp + 84)) 4 = Some (Z_to_le_bytes 4 w) ->
  rdn SEGS m (Z_to_bv 64 (sp + 88)) 8 = Some (Z_to_le_bytes 8 qtab) ->
  getr regs 2 = Z_to_bv 64 sp ->
  getr regs 5 = Z_to_bv 64 srow ->
  getr regs 6 = Z_to_bv 64 (j + 1) ->
  getr regs 7 = Z_to_bv 64 (srow + j + 1) ->
  getr regs 13 = Z_to_bv 64 1 ->
  getr regs 15 = Z_to_bv 64 1 ->
  getr regs 16 = Z_to_bv 64 3 ->
  getr regs 17 = Z_to_bv 64 drow ->
  getr regs 28 = Z_to_bv 64 (drow + j + 1) ->
  getr regs 29 = Z_to_bv 64 (drow + j + 1) ->
  getr regs 30 = Z_to_bv 64 (srow + j + 1) ->
  getr regs 31 = Z_to_bv 64 w ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1ddf0) m rom) (@mkst fx regs' (Z_to_bv 64 0x1dd70) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r []%list) regs regs'.
Proof using All.
  intros fx regs m  BT KC0 KC1 H2 H5 H6 H7 H13 H15 H16 H17 H28 H29 H30 H31.
  dl_facts.
  ex_entry regs [sp; drow; srow; qtab; w; j; (srow + j)%Z; (drow + j)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [sp; drow; srow; qtab; w; j; (srow + j)%Z; (drow + j)%Z]) m [KWord (SA (EVar 32) (84)) 4 (EVar 36); KWord (SA (EVar 32) (88)) 8 (EVar 35); KRange (EVar 32) 4096 140737488355328; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 1 20000; KRange (EVar 37) 0 19999; KRange (EVar 38) 4096 140737488375327; KRange (EVar 39) 4096 140737488375327]) by (ex_know regs).
  dl_run 400%nat [122064%Z; 122224%Z; 122352%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Local Abbreviation wp_1dc6c_cells := (wp_1dc6c_cells_def sp drow srow qtab w j wpld wplt).
Local Abbreviation wp_1dc6c_cells_w := (wp_1dc6c_cells_w_def sp drow srow qtab w j wpld wplt).
Lemma wp_1dc6c_path : forall (fx : FPState) regs m,
  cells_ok SEGS m wp_1dc6c_cells ->
  tab_rd SEGS true (fun _ => True) wp_1dc6c_cells_w m qtab ->
  (forall m', mframe wp_1dc6c_cells_w m m' -> rdn SEGS m' (Z_to_bv 64 (sp + 84)) 4 = Some (Z_to_le_bytes 4 w)) ->
  (forall m', mframe wp_1dc6c_cells_w m m' -> rdn SEGS m' (Z_to_bv 64 (sp + 88)) 8 = Some (Z_to_le_bytes 8 qtab)) ->
  getr regs 2 = Z_to_bv 64 sp ->
  getr regs 5 = Z_to_bv 64 srow ->
  getr regs 6 = Z_to_bv 64 j ->
  getr regs 7 = Z_to_bv 64 (srow + j) ->
  getr regs 13 = Z_to_bv 64 1 ->
  getr regs 15 = Z_to_bv 64 1 ->
  getr regs 16 = Z_to_bv 64 3 ->
  getr regs 17 = Z_to_bv 64 drow ->
  getr regs 28 = Z_to_bv 64 (drow + j) ->
  getr regs 29 = Z_to_bv 64 (drow + j) ->
  getr regs 30 = Z_to_bv 64 (srow + j) ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1dd70) m rom) (@mkst fx regs' (Z_to_bv 64 0x1ddf0) m' rom)
    /\ mframe wp_1dc6c_cells m m'
    /\ mframe wp_1dc6c_cells_w m m'
    /\ getr regs' 6 = Z_to_bv 64 (j + 1)
    /\ getr regs' 7 = Z_to_bv 64 (srow + j + 1)
    /\ getr regs' 8 = Z_to_bv 64 (bytea (drow + j))
    /\ getr regs' 22 = Z_to_bv 64 0
    /\ getr regs' 28 = Z_to_bv 64 (drow + j + 1)
    /\ getr regs' 29 = Z_to_bv 64 (drow + j + 1)
    /\ getr regs' 30 = Z_to_bv 64 (srow + j + 1)
    /\ getr regs' 31 = Z_to_bv 64 w
    /\ regs_agree (fun r => In r [6; 7; 8; 20; 22; 28; 29; 30; 31]%list) regs regs'.
Proof using All.
  intros fx regs m CK TR_qtab_true_4 KCM0 KCM1 H2 H5 H6 H7 H13 H15 H16 H17 H28 H29 H30.
  pose proof (mframe_refl wp_1dc6c_cells m) as FK0.
  pose proof (mframe_refl wp_1dc6c_cells_w m) as FW0.
  destruct (cells_ok_read SEGS m m wp_1dc6c_cells (bytea (srow + j))%Z 1%Z wr_readable_img CK (proj1 FK0) ltac:(dl_in0)) as [bs1_0 Rd1_0].
  destruct (TR_qtab_true_4 m (rdv false 1 bs1_0)%Z FW0 ltac:(dl_u8)) as (bs1_1 & Rd1_1 & TV1_1).
  destruct (wp_1dc6c fx regs m bs1_0 bs1_1 Rd1_0 Rd1_1 (cells_ok_sok SEGS m m wp_1dc6c_cells (bytea (drow + j))%Z 1%Z CK (proj1 FK0) ltac:(dl_in0)) (KCM0 m FW0) (KCM1 m FW0) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r1 & m1 & RUN1 & FR1 & E1_6 & E1_7 & E1_8 & E1_22 & E1_28 & E1_29 & E1_30 & E1_31 & AG1).
  assert (FK1 : mframe wp_1dc6c_cells m m1) by (apply (mframe_step _ _ _ _ _ FK0 FR1); unfold wp_1dc6c_cells_def; dl_incl).
  assert (FW1 : mframe wp_1dc6c_cells_w m m1) by (apply (mframe_step _ _ _ _ _ FW0 FR1); unfold wp_1dc6c_cells_w_def; dl_incl).
  exists r1, m1. split; [exact RUN1|]. split; [exact FK1|]. split; [exact FW1|].
  repeat split; [dl_get .. | ra_chain].
Qed.

End WP.

(* [comment removed for export] *)
Definition wl_hyps (sp datad datat w h wpld wplt i accd acct : Z) : Prop :=
  (4096 <= sp <= 140737488355328)%Z /\ (4096 <= datad <= 140737488355328)%Z /\ (datad mod 4 = 0)%Z /\ (4096 <= datat <= 140737488355328)%Z /\ (datat mod 4 = 0)%Z /\ (1 <= w <= 20000)%Z /\ (1 <= h <= 20000)%Z /\ (1 <= wpld <= 5000)%Z /\ (1 <= wplt <= 5000)%Z /\ (0 <= i <= 19999)%Z /\ (0 <= accd <= 67108864)%Z /\ (0 <= acct <= 67108864)%Z /\ (accd = i * wpld)%Z /\ (acct = i * wplt)%Z /\ (0 <= i * wpld < 2 ^ 26)%Z /\ (0 <= i * wplt < 2 ^ 26)%Z /\ (0 <= i < h)%Z /\ (0 <= (i + 1) * wpld < 2 ^ 26)%Z /\ (0 <= (i + 1) * wplt < 2 ^ 26)%Z.
Section WL.
Variable rom : word -> option byte.
Variables (sp datad datat w h wpld wplt i accd acct : Z).
Hypothesis HYP : wl_hyps sp datad datat w h wpld wplt i accd acct.
Ltac dl_facts := pose proof HYP as (R_sp & R_datad & A_datad & R_datat & A_datat & R_w & R_h & R_wpld & R_wplt & R_i & R_accd & R_acct & Ead & Eat & Hpd & Hpt & Hi & Hpd1 & Hpt1); idtac.
(* [comment removed for export] *)
Lemma wl_1dbcc : forall (fx : FPState) regs m ,
  rdn SEGS m (Z_to_bv 64 (sp + 80)) 4 = Some (Z_to_le_bytes 4 h) ->
  getr regs 2 = Z_to_bv 64 sp ->
  getr regs 9 = Z_to_bv 64 datat ->
  getr regs 10 = Z_to_bv 64 accd ->
  getr regs 11 = Z_to_bv 64 acct ->
  getr regs 12 = Z_to_bv 64 i ->
  getr regs 13 = Z_to_bv 64 1 ->
  getr regs 14 = Z_to_bv 64 wplt ->
  getr regs 15 = Z_to_bv 64 1 ->
  getr regs 16 = Z_to_bv 64 3 ->
  getr regs 18 = Z_to_bv 64 datad ->
  getr regs 19 = Z_to_bv 64 wpld ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1dcd0) m rom) (@mkst fx regs' (Z_to_bv 64 0x1dce0) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 10 = Z_to_bv 64 (accd + wpld)
    /\ getr regs' 11 = Z_to_bv 64 (acct + wplt)
    /\ getr regs' 12 = Z_to_bv 64 (i + 1)
    /\ getr regs' 17 = Z_to_bv 64 h
    /\ regs_agree (fun r => In r [10; 11; 12; 17]%list) regs regs'.
Proof using All.
  intros fx regs m  KC0 H2 H9 H10 H11 H12 H13 H14 H15 H16 H18 H19.
  dl_facts.
  ex_entry regs [sp; datad; datat; w; h; wpld; wplt; i; accd; acct; (accd + wpld)%Z; (acct + wplt)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [sp; datad; datat; w; h; wpld; wplt; i; accd; acct; (accd + wpld)%Z; (acct + wplt)%Z]) m [KWord (SA (EVar 32) (80)) 4 (EVar 36); KRange (EVar 32) 4096 140737488355328; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 1 20000; KRange (EVar 36) 1 20000; KRange (EVar 37) 1 5000; KRange (EVar 38) 1 5000; KRange (EVar 39) 0 19999; KRange (EVar 40) 0 67108864; KRange (EVar 41) 0 67108864; KRange (EVar 42) 1 67113864; KRange (EVar 43) 1 67113864]) by (ex_know regs).
  dl_run 400%nat [122084%Z; 122360%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma wl_1dbdcf : forall (fx : FPState) regs m ,
  branch_taken BC_GE (Z_to_bv 64 (i + 1)) (Z_to_bv 64 h) = false ->
  rdn SEGS m (Z_to_bv 64 (sp + 80)) 4 = Some (Z_to_le_bytes 4 h) ->
  getr regs 2 = Z_to_bv 64 sp ->
  getr regs 9 = Z_to_bv 64 datat ->
  getr regs 10 = Z_to_bv 64 (accd + wpld) ->
  getr regs 11 = Z_to_bv 64 (acct + wplt) ->
  getr regs 12 = Z_to_bv 64 (i + 1) ->
  getr regs 13 = Z_to_bv 64 1 ->
  getr regs 14 = Z_to_bv 64 wplt ->
  getr regs 15 = Z_to_bv 64 1 ->
  getr regs 16 = Z_to_bv 64 3 ->
  getr regs 17 = Z_to_bv 64 h ->
  getr regs 18 = Z_to_bv 64 datad ->
  getr regs 19 = Z_to_bv 64 wpld ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1dce0) m rom) (@mkst fx regs' (Z_to_bv 64 0x1dce4) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r []%list) regs regs'.
Proof using All.
  intros fx regs m  BT KC0 H2 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19.
  dl_facts.
  ex_entry regs [sp; datad; datat; w; h; wpld; wplt; i; accd; acct; (accd + wpld)%Z; (acct + wplt)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [sp; datad; datat; w; h; wpld; wplt; i; accd; acct; (accd + wpld)%Z; (acct + wplt)%Z]) m [KWord (SA (EVar 32) (80)) 4 (EVar 36); KRange (EVar 32) 4096 140737488355328; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 1 20000; KRange (EVar 36) 1 20000; KRange (EVar 37) 1 5000; KRange (EVar 38) 1 5000; KRange (EVar 39) 0 19999; KRange (EVar 40) 0 67108864; KRange (EVar 41) 0 67108864; KRange (EVar 42) 1 67113864; KRange (EVar 43) 1 67113864]) by (ex_know regs).
  dl_run 400%nat [122084%Z; 122360%Z] (SCR [false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma wl_1dbdct : forall (fx : FPState) regs m ,
  branch_taken BC_GE (Z_to_bv 64 (i + 1)) (Z_to_bv 64 h) = true ->
  rdn SEGS m (Z_to_bv 64 (sp + 80)) 4 = Some (Z_to_le_bytes 4 h) ->
  getr regs 2 = Z_to_bv 64 sp ->
  getr regs 9 = Z_to_bv 64 datat ->
  getr regs 10 = Z_to_bv 64 (accd + wpld) ->
  getr regs 11 = Z_to_bv 64 (acct + wplt) ->
  getr regs 12 = Z_to_bv 64 (i + 1) ->
  getr regs 13 = Z_to_bv 64 1 ->
  getr regs 14 = Z_to_bv 64 wplt ->
  getr regs 15 = Z_to_bv 64 1 ->
  getr regs 16 = Z_to_bv 64 3 ->
  getr regs 17 = Z_to_bv 64 h ->
  getr regs 18 = Z_to_bv 64 datad ->
  getr regs 19 = Z_to_bv 64 wpld ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1dce0) m rom) (@mkst fx regs' (Z_to_bv 64 0x1ddf8) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r []%list) regs regs'.
Proof using All.
  intros fx regs m  BT KC0 H2 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19.
  dl_facts.
  ex_entry regs [sp; datad; datat; w; h; wpld; wplt; i; accd; acct; (accd + wpld)%Z; (acct + wplt)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [sp; datad; datat; w; h; wpld; wplt; i; accd; acct; (accd + wpld)%Z; (acct + wplt)%Z]) m [KWord (SA (EVar 32) (80)) 4 (EVar 36); KRange (EVar 32) 4096 140737488355328; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 1 20000; KRange (EVar 36) 1 20000; KRange (EVar 37) 1 5000; KRange (EVar 38) 1 5000; KRange (EVar 39) 0 19999; KRange (EVar 40) 0 67108864; KRange (EVar 41) 0 67108864; KRange (EVar 42) 1 67113864; KRange (EVar 43) 1 67113864]) by (ex_know regs).
  dl_run 400%nat [122084%Z; 122360%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

End WL.
