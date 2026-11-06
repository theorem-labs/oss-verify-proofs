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
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import WalksLib W2Lib LeptStructs LeptExec DitherLib DitherTac DitherLib2 DitherTac2 DitherTab DitherTab1.
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

(* [comment removed for export] *)
Definition qa_hyps (sp qtab w h wpld wplt : Z) : Prop :=
  (4096 <= sp <= 140737488355328)%Z /\ (4096 <= qtab <= 140737488355328)%Z /\ (qtab mod 4 = 0)%Z /\ (1 <= w <= 20000)%Z /\ (1 <= h <= 20000)%Z /\ (1 <= wpld <= 5000)%Z /\ (1 <= wplt <= 5000)%Z.
Section QA.
Variable rom : word -> option byte.
Variables (sp qtab w h wpld wplt : Z).
Hypothesis HYP : qa_hyps sp qtab w h wpld wplt.
Ltac dl_facts := pose proof HYP as (R_sp & R_qtab & A_qtab & R_w & R_h & R_wpld & R_wplt); idtac.
(* [comment removed for export] *)
Lemma qa_1be14 : forall (fx : FPState) regs m ,
  rdn SEGS m (Z_to_bv 64 (sp + 48)) 4 = Some (Z_to_le_bytes 4 h) ->
  rdn SEGS m (Z_to_bv 64 (sp + 52)) 4 = Some (Z_to_le_bytes 4 w) ->
  rdn SEGS m (Z_to_bv 64 (sp + 56)) 8 = Some (Z_to_le_bytes 8 qtab) ->
  getr regs 2 = Z_to_bv 64 sp ->
  getr regs 11 = Z_to_bv 64 h ->
  getr regs 14 = Z_to_bv 64 wplt ->
  getr regs 19 = Z_to_bv 64 wpld ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1bf10) m rom) (@mkst fx regs' (Z_to_bv 64 0x1bf38) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 10 = Z_to_bv 64 0
    /\ getr regs' 12 = Z_to_bv 64 w
    /\ getr regs' 14 = Z_to_bv 64 (4 * wplt)
    /\ getr regs' 19 = Z_to_bv 64 (4 * wpld)
    /\ regs_agree (fun r => In r [10; 12; 14; 19]%list) regs regs'.
Proof using All.
  intros fx regs m  KC0 KC1 KC2 H2 H11 H14 H19.
  dl_facts.
  ex_entry regs [sp; qtab; w; h; wpld; wplt] HR.
  assert (HK : know_ok SEGS (ex_env regs [sp; qtab; w; h; wpld; wplt]) m [KWord (SA (EVar 32) (48)) 4 (EVar 35); KWord (SA (EVar 32) (52)) 4 (EVar 34); KWord (SA (EVar 32) (56)) 8 (EVar 33); KRange (EVar 32) 4096 140737488355328; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 1 20000; KRange (EVar 35) 1 20000; KRange (EVar 36) 1 5000; KRange (EVar 37) 1 5000]) by (ex_know regs).
  dl_run 400%nat [114488%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

End QA.

(* [comment removed for export] *)
Definition qr_hyps (sp drow srow w : Z) : Prop :=
  (4096 <= sp <= 140737488355328)%Z /\ (4096 <= drow <= 140737488355328)%Z /\ (drow mod 4 = 0)%Z /\ (4096 <= srow <= 140737488355328)%Z /\ (srow mod 4 = 0)%Z /\ (1 <= w <= 20000)%Z.
Section QR.
Variable rom : word -> option byte.
Variables (sp drow srow w : Z).
Hypothesis HYP : qr_hyps sp drow srow w.
Ltac dl_facts := pose proof HYP as (R_sp & R_drow & A_drow & R_srow & A_srow & R_w); idtac.
(* [comment removed for export] *)
Lemma qr_1be3c : forall (fx : FPState) regs m ,
  getr regs 2 = Z_to_bv 64 sp ->
  getr regs 9 = Z_to_bv 64 drow ->
  getr regs 12 = Z_to_bv 64 w ->
  getr regs 18 = Z_to_bv 64 srow ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1bf38) m rom) (@mkst fx regs' (Z_to_bv 64 0x1bf48) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 11 = Z_to_bv 64 0
    /\ getr regs' 13 = Z_to_bv 64 srow
    /\ getr regs' 15 = Z_to_bv 64 drow
    /\ regs_agree (fun r => In r [11; 13; 15]%list) regs regs'.
Proof using All.
  intros fx regs m  H2 H9 H12 H18.
  dl_facts.
  ex_entry regs [sp; drow; srow; w] HR.
  assert (HK : know_ok SEGS (ex_env regs [sp; drow; srow; w]) m [KRange (EVar 32) 4096 140737488355328; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 1 20000]) by (ex_know regs).
  dl_run 400%nat [114504%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

End QR.

Definition qp_1be4c_cells_def (sp drow srow qtab w h j wpld wplt : Z) : list (Z * Z) := [((bytea (srow + j))%Z, 1%Z); ((bytea (drow + j))%Z, 1%Z)].
Definition qp_1be4c_cells_w_def (sp drow srow qtab w h j wpld wplt : Z) : list (Z * Z) := [((bytea (drow + j))%Z, 1%Z)].
(* [comment removed for export] *)
Definition qp_hyps (sp drow srow qtab w h j wpld wplt : Z) : Prop :=
  (4096 <= sp <= 140737488355328)%Z /\ (4096 <= drow <= 140737488355328)%Z /\ (drow mod 4 = 0)%Z /\ (4096 <= srow <= 140737488355328)%Z /\ (srow mod 4 = 0)%Z /\ (4096 <= qtab <= 140737488355328)%Z /\ (qtab mod 4 = 0)%Z /\ (1 <= w <= 20000)%Z /\ (1 <= h <= 20000)%Z /\ (0 <= j <= 19999)%Z /\ (0 <= j < w)%Z /\ (w <= 4 * wpld)%Z /\ (w <= 4 * wplt)%Z /\ dapart drow (4 * wpld) sp 64.
Section QP.
Variable rom : word -> option byte.
Variables (sp drow srow qtab w h j wpld wplt : Z).
Hypothesis HYP : qp_hyps sp drow srow qtab w h j wpld wplt.
Ltac dl_facts := pose proof HYP as (R_sp & R_drow & A_drow & R_srow & A_srow & R_qtab & A_qtab & R_w & R_h & R_j & Hj & Hwd & Hwt & AP_df); destruct (al4_ex _ A_drow) as [cd Ecd]; destruct (al4_ex _ A_srow) as [cs Ecs].
(* [comment removed for export] *)
Lemma qp_1be4c : forall (fx : FPState) regs m (bs0 : list byte) (bs1 : list byte),
  rdn SEGS m (Z_to_bv 64 (bytea (srow + j))) 1 = Some bs0 ->
  rdn SEGS m (Z_to_bv 64 (qtab + (4 * (rdv false 1 bs0)))) 1 = Some bs1 ->
  store_ok SEGS m (Z_to_bv 64 (bytea (drow + j))) 1 = true ->
  rdn SEGS m (Z_to_bv 64 (sp + 48)) 4 = Some (Z_to_le_bytes 4 h) ->
  rdn SEGS m (Z_to_bv 64 (sp + 52)) 4 = Some (Z_to_le_bytes 4 w) ->
  rdn SEGS m (Z_to_bv 64 (sp + 56)) 8 = Some (Z_to_le_bytes 8 qtab) ->
  getr regs 2 = Z_to_bv 64 sp ->
  getr regs 11 = Z_to_bv 64 j ->
  getr regs 13 = Z_to_bv 64 (srow + j) ->
  getr regs 15 = Z_to_bv 64 (drow + j) ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1bf48) m rom) (@mkst fx regs' (Z_to_bv 64 0x1bf78) m' rom)
    /\ mframe [((bytea (drow + j))%Z, 1%Z)] m m'
    /\ getr regs' 11 = Z_to_bv 64 (j + 1)
    /\ getr regs' 12 = Z_to_bv 64 w
    /\ getr regs' 13 = Z_to_bv 64 (srow + j + 1)
    /\ getr regs' 15 = Z_to_bv 64 (drow + j + 1)
    /\ getr regs' 16 = Z_to_bv 64 (bytea (drow + j))
    /\ regs_agree (fun r => In r [11; 12; 13; 15; 16]%list) regs regs'.
Proof using All.
  intros fx regs m bs0 bs1 R0 R1 S0 KC0 KC1 KC2 H2 H11 H13 H15.
  dl_facts.
  pose proof (rdv_u8 SEGS _ _ _ R0) as U0.
  pose proof (rdv_u8 SEGS _ _ _ R1) as U1.
  ex_entry regs [sp; drow; srow; qtab; w; h; j; (srow + j)%Z; (drow + j)%Z; rdv false 1 bs0; rdv false 1 bs1] HR.
  assert (HK : know_ok SEGS (ex_env regs [sp; drow; srow; qtab; w; h; j; (srow + j)%Z; (drow + j)%Z; rdv false 1 bs0; rdv false 1 bs1]) m [KWord (SA (EVar 32) (48)) 4 (EVar 37); KWord (SA (EVar 32) (52)) 4 (EVar 36); KWord (SA (EVar 32) (56)) 8 (EVar 35); KRange (EVar 32) 4096 140737488355328; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 1 20000; KRange (EVar 37) 1 20000; KRange (EVar 38) 0 19999; KRange (EVar 39) 4096 140737488375327; KRange (EVar 40) 4096 140737488375327]) by (ex_know regs).
  dl_run 400%nat [114504%Z; 114552%Z; 114556%Z] (SCR [] [EVar 41; EVar 42] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma qp_1be7cf : forall (fx : FPState) regs m ,
  branch_taken BC_LT (Z_to_bv 64 (j + 1)) (Z_to_bv 64 w) = false ->
  rdn SEGS m (Z_to_bv 64 (sp + 48)) 4 = Some (Z_to_le_bytes 4 h) ->
  rdn SEGS m (Z_to_bv 64 (sp + 52)) 4 = Some (Z_to_le_bytes 4 w) ->
  rdn SEGS m (Z_to_bv 64 (sp + 56)) 8 = Some (Z_to_le_bytes 8 qtab) ->
  getr regs 2 = Z_to_bv 64 sp ->
  getr regs 11 = Z_to_bv 64 (j + 1) ->
  getr regs 12 = Z_to_bv 64 w ->
  getr regs 13 = Z_to_bv 64 (srow + j + 1) ->
  getr regs 15 = Z_to_bv 64 (drow + j + 1) ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1bf78) m rom) (@mkst fx regs' (Z_to_bv 64 0x1bf7c) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r []%list) regs regs'.
Proof using All.
  intros fx regs m  BT KC0 KC1 KC2 H2 H11 H12 H13 H15.
  dl_facts.
  ex_entry regs [sp; drow; srow; qtab; w; h; j; (srow + j)%Z; (drow + j)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [sp; drow; srow; qtab; w; h; j; (srow + j)%Z; (drow + j)%Z]) m [KWord (SA (EVar 32) (48)) 4 (EVar 37); KWord (SA (EVar 32) (52)) 4 (EVar 36); KWord (SA (EVar 32) (56)) 8 (EVar 35); KRange (EVar 32) 4096 140737488355328; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 1 20000; KRange (EVar 37) 1 20000; KRange (EVar 38) 0 19999; KRange (EVar 39) 4096 140737488375327; KRange (EVar 40) 4096 140737488375327]) by (ex_know regs).
  dl_run 400%nat [114504%Z; 114552%Z; 114556%Z] (SCR [false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma qp_1be7ct : forall (fx : FPState) regs m ,
  branch_taken BC_LT (Z_to_bv 64 (j + 1)) (Z_to_bv 64 w) = true ->
  rdn SEGS m (Z_to_bv 64 (sp + 48)) 4 = Some (Z_to_le_bytes 4 h) ->
  rdn SEGS m (Z_to_bv 64 (sp + 52)) 4 = Some (Z_to_le_bytes 4 w) ->
  rdn SEGS m (Z_to_bv 64 (sp + 56)) 8 = Some (Z_to_le_bytes 8 qtab) ->
  getr regs 2 = Z_to_bv 64 sp ->
  getr regs 11 = Z_to_bv 64 (j + 1) ->
  getr regs 12 = Z_to_bv 64 w ->
  getr regs 13 = Z_to_bv 64 (srow + j + 1) ->
  getr regs 15 = Z_to_bv 64 (drow + j + 1) ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1bf78) m rom) (@mkst fx regs' (Z_to_bv 64 0x1bf48) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r []%list) regs regs'.
Proof using All.
  intros fx regs m  BT KC0 KC1 KC2 H2 H11 H12 H13 H15.
  dl_facts.
  ex_entry regs [sp; drow; srow; qtab; w; h; j; (srow + j)%Z; (drow + j)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [sp; drow; srow; qtab; w; h; j; (srow + j)%Z; (drow + j)%Z]) m [KWord (SA (EVar 32) (48)) 4 (EVar 37); KWord (SA (EVar 32) (52)) 4 (EVar 36); KWord (SA (EVar 32) (56)) 8 (EVar 35); KRange (EVar 32) 4096 140737488355328; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 1 20000; KRange (EVar 37) 1 20000; KRange (EVar 38) 0 19999; KRange (EVar 39) 4096 140737488375327; KRange (EVar 40) 4096 140737488375327]) by (ex_know regs).
  dl_run 400%nat [114504%Z; 114552%Z; 114556%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Local Abbreviation qp_1be4c_cells := (qp_1be4c_cells_def sp drow srow qtab w h j wpld wplt).
Local Abbreviation qp_1be4c_cells_w := (qp_1be4c_cells_w_def sp drow srow qtab w h j wpld wplt).
Lemma qp_1be4c_path : forall (fx : FPState) regs m,
  cells_ok SEGS m qp_1be4c_cells ->
  tab_rdn SEGS 1 false (fun _ => True) qp_1be4c_cells_w m qtab ->
  (forall m', mframe qp_1be4c_cells_w m m' -> rdn SEGS m' (Z_to_bv 64 (sp + 48)) 4 = Some (Z_to_le_bytes 4 h)) ->
  (forall m', mframe qp_1be4c_cells_w m m' -> rdn SEGS m' (Z_to_bv 64 (sp + 52)) 4 = Some (Z_to_le_bytes 4 w)) ->
  (forall m', mframe qp_1be4c_cells_w m m' -> rdn SEGS m' (Z_to_bv 64 (sp + 56)) 8 = Some (Z_to_le_bytes 8 qtab)) ->
  getr regs 2 = Z_to_bv 64 sp ->
  getr regs 11 = Z_to_bv 64 j ->
  getr regs 13 = Z_to_bv 64 (srow + j) ->
  getr regs 15 = Z_to_bv 64 (drow + j) ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1bf48) m rom) (@mkst fx regs' (Z_to_bv 64 0x1bf78) m' rom)
    /\ mframe qp_1be4c_cells m m'
    /\ mframe qp_1be4c_cells_w m m'
    /\ getr regs' 11 = Z_to_bv 64 (j + 1)
    /\ getr regs' 12 = Z_to_bv 64 w
    /\ getr regs' 13 = Z_to_bv 64 (srow + j + 1)
    /\ getr regs' 15 = Z_to_bv 64 (drow + j + 1)
    /\ getr regs' 16 = Z_to_bv 64 (bytea (drow + j))
    /\ regs_agree (fun r => In r [11; 12; 13; 15; 16]%list) regs regs'.
Proof using All.
  intros fx regs m CK TR_qtab_false_1 KCM0 KCM1 KCM2 H2 H11 H13 H15.
  pose proof (mframe_refl qp_1be4c_cells m) as FK0.
  pose proof (mframe_refl qp_1be4c_cells_w m) as FW0.
  destruct (cells_ok_read SEGS m m qp_1be4c_cells (bytea (srow + j))%Z 1%Z wr_readable_img CK (proj1 FK0) ltac:(dl_in0)) as [bs1_0 Rd1_0].
  destruct (TR_qtab_false_1 m (rdv false 1 bs1_0)%Z FW0 ltac:(dl_u8)) as (bs1_1 & Rd1_1 & TV1_1).
  destruct (qp_1be4c fx regs m bs1_0 bs1_1 Rd1_0 Rd1_1 (cells_ok_sok SEGS m m qp_1be4c_cells (bytea (drow + j))%Z 1%Z CK (proj1 FK0) ltac:(dl_in0)) (KCM0 m FW0) (KCM1 m FW0) (KCM2 m FW0) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r1 & m1 & RUN1 & FR1 & E1_11 & E1_12 & E1_13 & E1_15 & E1_16 & AG1).
  assert (FK1 : mframe qp_1be4c_cells m m1) by (apply (mframe_step _ _ _ _ _ FK0 FR1); unfold qp_1be4c_cells_def; dl_incl).
  assert (FW1 : mframe qp_1be4c_cells_w m m1) by (apply (mframe_step _ _ _ _ _ FW0 FR1); unfold qp_1be4c_cells_w_def; dl_incl).
  exists r1, m1. split; [exact RUN1|]. split; [exact FK1|]. split; [exact FW1|].
  repeat split; [dl_get .. | ra_chain].
Qed.

End QP.

(* [comment removed for export] *)
Definition ql_hyps (sp drow srow qtab w h i d4 s4 : Z) : Prop :=
  (4096 <= sp <= 140737488355328)%Z /\ (4096 <= drow <= 140737488355328)%Z /\ (drow mod 4 = 0)%Z /\ (4096 <= srow <= 140737488355328)%Z /\ (srow mod 4 = 0)%Z /\ (4096 <= qtab <= 140737488355328)%Z /\ (qtab mod 4 = 0)%Z /\ (1 <= w <= 20000)%Z /\ (1 <= h <= 20000)%Z /\ (0 <= i <= 19999)%Z /\ (4 <= d4 <= 20000)%Z /\ (d4 mod 4 = 0)%Z /\ (4 <= s4 <= 20000)%Z /\ (s4 mod 4 = 0)%Z /\ (0 <= i < h)%Z.
Section QL.
Variable rom : word -> option byte.
Variables (sp drow srow qtab w h i d4 s4 : Z).
Hypothesis HYP : ql_hyps sp drow srow qtab w h i d4 s4.
Ltac dl_facts := pose proof HYP as (R_sp & R_drow & A_drow & R_srow & A_srow & R_qtab & A_qtab & R_w & R_h & R_i & R_d4 & A_d4 & R_s4 & A_s4 & Hi); idtac.
(* [comment removed for export] *)
Lemma ql_1be38f : forall (fx : FPState) regs m ,
  branch_taken BC_GE (Z_to_bv 64 (i + 1)) (Z_to_bv 64 h) = false ->
  rdn SEGS m (Z_to_bv 64 (sp + 48)) 4 = Some (Z_to_le_bytes 4 h) ->
  rdn SEGS m (Z_to_bv 64 (sp + 52)) 4 = Some (Z_to_le_bytes 4 w) ->
  rdn SEGS m (Z_to_bv 64 (sp + 56)) 8 = Some (Z_to_le_bytes 8 qtab) ->
  getr regs 2 = Z_to_bv 64 sp ->
  getr regs 9 = Z_to_bv 64 (drow + d4) ->
  getr regs 10 = Z_to_bv 64 (i + 1) ->
  getr regs 11 = Z_to_bv 64 h ->
  getr regs 14 = Z_to_bv 64 s4 ->
  getr regs 18 = Z_to_bv 64 (srow + s4) ->
  getr regs 19 = Z_to_bv 64 d4 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1bf34) m rom) (@mkst fx regs' (Z_to_bv 64 0x1bf38) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r []%list) regs regs'.
Proof using All.
  intros fx regs m  BT KC0 KC1 KC2 H2 H9 H10 H11 H14 H18 H19.
  dl_facts.
  ex_entry regs [sp; drow; srow; qtab; w; h; i; d4; s4; (drow + d4)%Z; (srow + s4)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [sp; drow; srow; qtab; w; h; i; d4; s4; (drow + d4)%Z; (srow + s4)%Z]) m [KWord (SA (EVar 32) (48)) 4 (EVar 37); KWord (SA (EVar 32) (52)) 4 (EVar 36); KWord (SA (EVar 32) (56)) 8 (EVar 35); KRange (EVar 32) 4096 140737488355328; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 1 20000; KRange (EVar 37) 1 20000; KRange (EVar 38) 0 19999; KRange (EVar 39) 4 20000; KAlign (EVar 39) 4; KRange (EVar 40) 4 20000; KAlign (EVar 40) 4; KRange (EVar 41) 4100 140737488375328; KRange (EVar 42) 4100 140737488375328]) by (ex_know regs).
  dl_run 400%nat [114488%Z; 114564%Z] (SCR [false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma ql_1be38t : forall (fx : FPState) regs m ,
  branch_taken BC_GE (Z_to_bv 64 (i + 1)) (Z_to_bv 64 h) = true ->
  rdn SEGS m (Z_to_bv 64 (sp + 48)) 4 = Some (Z_to_le_bytes 4 h) ->
  rdn SEGS m (Z_to_bv 64 (sp + 52)) 4 = Some (Z_to_le_bytes 4 w) ->
  rdn SEGS m (Z_to_bv 64 (sp + 56)) 8 = Some (Z_to_le_bytes 8 qtab) ->
  getr regs 2 = Z_to_bv 64 sp ->
  getr regs 9 = Z_to_bv 64 (drow + d4) ->
  getr regs 10 = Z_to_bv 64 (i + 1) ->
  getr regs 11 = Z_to_bv 64 h ->
  getr regs 14 = Z_to_bv 64 s4 ->
  getr regs 18 = Z_to_bv 64 (srow + s4) ->
  getr regs 19 = Z_to_bv 64 d4 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1bf34) m rom) (@mkst fx regs' (Z_to_bv 64 0x1bf84) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r []%list) regs regs'.
Proof using All.
  intros fx regs m  BT KC0 KC1 KC2 H2 H9 H10 H11 H14 H18 H19.
  dl_facts.
  ex_entry regs [sp; drow; srow; qtab; w; h; i; d4; s4; (drow + d4)%Z; (srow + s4)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [sp; drow; srow; qtab; w; h; i; d4; s4; (drow + d4)%Z; (srow + s4)%Z]) m [KWord (SA (EVar 32) (48)) 4 (EVar 37); KWord (SA (EVar 32) (52)) 4 (EVar 36); KWord (SA (EVar 32) (56)) 8 (EVar 35); KRange (EVar 32) 4096 140737488355328; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 1 20000; KRange (EVar 37) 1 20000; KRange (EVar 38) 0 19999; KRange (EVar 39) 4 20000; KAlign (EVar 39) 4; KRange (EVar 40) 4 20000; KAlign (EVar 40) 4; KRange (EVar 41) 4100 140737488375328; KRange (EVar 42) 4100 140737488375328]) by (ex_know regs).
  dl_run 400%nat [114488%Z; 114564%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma ql_1be80 : forall (fx : FPState) regs m ,
  rdn SEGS m (Z_to_bv 64 (sp + 48)) 4 = Some (Z_to_le_bytes 4 h) ->
  rdn SEGS m (Z_to_bv 64 (sp + 52)) 4 = Some (Z_to_le_bytes 4 w) ->
  rdn SEGS m (Z_to_bv 64 (sp + 56)) 8 = Some (Z_to_le_bytes 8 qtab) ->
  getr regs 2 = Z_to_bv 64 sp ->
  getr regs 9 = Z_to_bv 64 drow ->
  getr regs 10 = Z_to_bv 64 i ->
  getr regs 14 = Z_to_bv 64 s4 ->
  getr regs 18 = Z_to_bv 64 srow ->
  getr regs 19 = Z_to_bv 64 d4 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1bf7c) m rom) (@mkst fx regs' (Z_to_bv 64 0x1bf34) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 9 = Z_to_bv 64 (drow + d4)
    /\ getr regs' 10 = Z_to_bv 64 (i + 1)
    /\ getr regs' 11 = Z_to_bv 64 h
    /\ getr regs' 18 = Z_to_bv 64 (srow + s4)
    /\ regs_agree (fun r => In r [9; 10; 11; 18]%list) regs regs'.
Proof using All.
  intros fx regs m  KC0 KC1 KC2 H2 H9 H10 H14 H18 H19.
  dl_facts.
  ex_entry regs [sp; drow; srow; qtab; w; h; i; d4; s4; (drow + d4)%Z; (srow + s4)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [sp; drow; srow; qtab; w; h; i; d4; s4; (drow + d4)%Z; (srow + s4)%Z]) m [KWord (SA (EVar 32) (48)) 4 (EVar 37); KWord (SA (EVar 32) (52)) 4 (EVar 36); KWord (SA (EVar 32) (56)) 8 (EVar 35); KRange (EVar 32) 4096 140737488355328; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 1 20000; KRange (EVar 37) 1 20000; KRange (EVar 38) 0 19999; KRange (EVar 39) 4 20000; KAlign (EVar 39) 4; KRange (EVar 40) 4 20000; KAlign (EVar 40) 4; KRange (EVar 41) 4100 140737488375328; KRange (EVar 42) 4100 140737488375328]) by (ex_know regs).
  dl_run 400%nat [114488%Z; 114564%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

End QL.
