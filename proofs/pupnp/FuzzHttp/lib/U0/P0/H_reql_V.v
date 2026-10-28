(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From stdpp Require Import base list.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Arr.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import ScanInt.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs F_syscalls Stdio_base F_shgetc_A F_shgetc_B F_strtol F_vfscanf_lib F_sscanf H_map_str_to_int H_memptr_cmp H_presp_A H_presp_B.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import H_reql_A.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling.
Import ListNotations.
Open Scope Z_scope.
Set Printing Width 1000.
Set Printing Depth 100.

Notation zb := (Z_to_bv 8 0).

Definition hiddenV (P : Prop) := P.
Ltac stash H := lazymatch type of H with hiddenV _ => idtac | ?T => change T with (hiddenV T) in H end.
Ltac unstash := unfold hiddenV in *.

Lemma rw_cells_C8_C44s : forall m X (w : word),
  rw_cells rsegs m X [C8 w] -> exists a b : word, rw_cells rsegs m X [C4 a; C4 b] /\ le_bytes_to_word (le4 a ++ le4 b) = w.
Proof.
  intros m X w H.
  pose proof (rw_cells_split_CB rsegs m X [] 8 (le8 w) [] [4; 4]%nat) as SP. cbn [app mk_CB_cells] in SP.
  assert (H8 : rw_cells rsegs m X [CB 8 (le8 w)]).
  { destruct H as [[W B] R]. split; [split; [cbn; split; [reflexivity| exact I]| exact B]| exact R]. }
  specialize (SP H8 eq_refl).
  pose proof (rw_cells_CB_C4 rsegs m X [] (firstn 4 (le8 w)) [CB 4 (firstn 4 (skipn 4 (le8 w)))] SP) as S1. cbn [app] in S1.
  pose proof (rw_cells_CB_C4 rsegs m X [C4 (le_bytes_to_word (firstn 4 (le8 w)))] (firstn 4 (skipn 4 (le8 w))) [] S1) as S2. cbn [app] in S2.
  eexists _, _. split; [exact S2|].
  pose proof (length_le8 w) as L8.
  rewrite !le4_of_bytes by (rewrite ?firstn_length, ?length_firstn, ?skipn_length, ?length_skipn; lia).
  rewrite (firstn_all2 (skipn 4 (le8 w))) by (rewrite length_skipn; lia). rewrite firstn_skipn. apply le_bytes_to_word_le8.
Qed.

Section VT.
Context {HCEIL : HasCeiling}.
  Hypothesis SNC : strncasecmp_stmt.
  Variables (P q lo : Z).
  Notation S := (P + 480)%Z.
  Notation MB := (P + 400)%Z.
  Hypothesis QLO : (lo + 1096 <= q)%Z.
  Hypothesis LO0 : (0x5d000 <= lo)%Z.
  Hypothesis QP : (q + 208 <= P)%Z.
  Hypothesis PHI : (P + 504 < 2^62)%Z.
  Variable mws : list word.
  Hypothesis MWSL : length mws = 22%nat.
  Hypothesis MID : forall i, (0 <= i < 11)%Z -> exists id, nth_error mws (Z.to_nat (2 * i + 1)) = Some (wz id) /\ (0 <= id <= 11)%Z.
  Hypothesis MT : table_strings mws 11 lo.

  #[using="QLO mws MWSL"] Lemma QLO1 : (lo <= q)%Z. Proof. lia. Qed.
  #[using="PHI mws MWSL"] Lemma PHI63 : (P + 504 < 2^63)%Z. Proof. lia. Qed.
  #[using="MWSL MID"] Lemma MID' : forall i, (0 <= i < 11)%Z -> exists id, nth_error mws (Z.to_nat (2 * i + 1)) = Some (wz id) /\ (0 <= id < 64)%Z.
  Proof. intros i Hi. destruct (MID i Hi) as (id & H1 & H2). exists id. split; [exact H1| lia]. Qed.

  Notation PRS pc x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 gp tp F fc m :=
    (MS (mkR x1 (wz q) gp tp t0 t1 t2 (wz P) (wz S) a0 a1 a2 a3 a4 a5 a6 a7 (wz (-1)) (wz 47) (wz 2) (wz FMT09) (wz MTAB) s7v (wz 3) s9v (wz 1) (wz 4) t3 t4 t5 t6)
        F (wz pc) fc None m (seg_rom rsegs)).
  Notation S7 := (wz (P + 8)). Notation S8 := (wz (P + 276)). Notation S9 := (wz (P + 280)).

  #[using="mws MWSL"] Lemma rq_mreq : forall (r : Z) (ub ul : word) gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
    mem_inv rsegs m -> rw_cells rsegs m (q + 56) [C8 ub; C8 ul] -> (0 <= r <= 5)%Z ->
    evt rsegs (fun ms' =>
        ( r <> 4 /\ ms' = PRS HEAD x1 t0 t1 t2 (wz r) a1 a2 a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 gp tp F fc m)
     \/ ( r = 4 /\ ms' = PRS 0x15dd8 x1 t0 t1 t2 ub a1 ul a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 gp tp F fc m))
      (PRS 0x15dcc x1 t0 t1 t2 (wz r) a1 a2 a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 gp tp F fc m).
  Proof.
    intros until m. intros MI Q40 RR.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    zstep. if_cases K; zify_cond K; condn K.
    - apply evt_done. left. split; [lia| reflexivity].
    - zstep. zstep. apply evt_done. right. split; [lia| reflexivity].
  Qed.

  #[using="mws MWSL"] Lemma table_strings_monoV : forall ws ne B B', table_strings ws ne B -> (B <= B')%Z -> table_strings ws ne B'.
  Proof.
    intros ws ne B B' TS LE i Hi. destruct (TS i Hi) as (Sx & str & slack & H1 & H2 & H3 & H4 & H5).
    exists Sx, str, slack. repeat (split; [assumption|]). lia.
  Qed.
End VT.

