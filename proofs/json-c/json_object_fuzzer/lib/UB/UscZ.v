(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q8l1.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UDgQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UDgQ.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
Import ListNotations. Unset Keyed Unification. Local Ltac Q2qa.Mq0.sf_vocab ::= Q2qa.Mq0.mkr__sf_vocab_5. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_step_core ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX.mkr__sg_step_core_3. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_zstep ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX.mkr__sg_zstep_4. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.G Require T_shp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module GwI.
Definition segs := rsegs.
End GwI.

Notation shp := G.T_shp.shp.
Notation S8 := G.T_shp.S8.
Notation S4 := G.T_shp.S4.
Notation SB4 := G.T_shp.SB4.
Definition shp_size (s : shp) : nat := match s with S8 => 8 | _ => 4 end%nat.
Lemma gw_eq_shp_size : @shp_size = ltac:(GwInst.gw_term (@Q8l1.Mq2.shp_size) (@shp_size)). Proof. unfold shp_size, Q8l1.Mq2.shp_size; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_shp_size : gw_eqs.
Fixpoint shp_sum (pat : list shp) : nat := match pat with [] => 0 | s :: pat' => shp_size s + shp_sum pat' end%nat.
Lemma gw_eq_shp_sum : @shp_sum = ltac:(GwInst.gw_term (@Q8l1.Mq2.shp_sum) (@shp_sum)). Proof. unfold shp_sum, Q8l1.Mq2.shp_sum; rewrite ?gw_eq_shp_size; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_shp_sum : gw_eqs.
Fixpoint shape_cells (pat : list shp) (bs : list byte) : list cell :=
match pat with
| [] => []
| s :: pat' =>
match s with
| S8 => C8 (le_bytes_to_word (firstn 8 bs)) :: shape_cells pat' (skipn 8 bs)
| S4 => C4 (le_bytes_to_word (firstn 4 bs)) :: shape_cells pat' (skipn 4 bs)
| SB4 => CB 4 (firstn 4 bs) :: shape_cells pat' (skipn 4 bs)
end
end.
Lemma gw_eq_shape_cells : @shape_cells = ltac:(GwInst.gw_term (@Q8l1.Mq2.shape_cells) (@shape_cells)). Proof. unfold shape_cells, Q8l1.Mq2.shape_cells; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_shape_cells : gw_eqs.

Lemma le8_of_bytes : forall bs : list byte, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof. first [GwInst.gw_exact (@Q8l1.Mq2.le8_of_bytes) | autorewrite with gw_eqs; GwInst.gw_exact (@Q8l1.Mq2.le8_of_bytes)]. Qed.
Lemma le4_of_bytes : forall bs : list byte, length bs = 4%nat -> le4 (le_bytes_to_word bs) = bs.
Proof. first [GwInst.gw_exact (@Q8l1.Mq2.le4_of_bytes) | autorewrite with gw_eqs; GwInst.gw_exact (@Q8l1.Mq2.le4_of_bytes)]. Qed.

Lemma shape_wf : forall pat bs, length bs = shp_sum pat -> cells_wf (shape_cells pat bs).
Proof. rewrite ?gw_eq_shp_sum, ?gw_eq_shape_cells; first [GwInst.gw_exact (@Q8l1.Mq2.shape_wf) | autorewrite with gw_eqs; GwInst.gw_exact (@Q8l1.Mq2.shape_wf)]. Qed.
Lemma shape_bytes : forall pat bs, length bs = shp_sum pat -> cells_bytes (shape_cells pat bs) = bs.
Proof. rewrite ?gw_eq_shp_sum, ?gw_eq_shape_cells; first [GwInst.gw_exact (@Q8l1.Mq2.shape_bytes) | autorewrite with gw_eqs; GwInst.gw_exact (@Q8l1.Mq2.shape_bytes)]. Qed.
Lemma shape_size : forall pat bs, cells_size (shape_cells pat bs) = shp_sum pat.
Proof. rewrite ?gw_eq_shp_sum, ?gw_eq_shape_cells; first [GwInst.gw_exact (@Q8l1.Mq2.shape_size) | autorewrite with gw_eqs; GwInst.gw_exact (@Q8l1.Mq2.shape_size)]. Qed.

Lemma rw_cells_reshape : ltac2:(Q6nq.tyx '(@Q8l1.Mq2.rw_cells_reshape) [[@gw_eq_shp_size__3; @gw_eq_shp_size__2; @gw_eq_shp_size]; [@gw_eq_shp_sum__3; @gw_eq_shp_sum__2; @gw_eq_shp_sum]; [@gw_eq_shape_cells__3; @gw_eq_shape_cells__2; @gw_eq_shape_cells]] '(@nil Z) 'Q6nq.gwt_nil).
Proof. first [GwInst.gw_exact (@Q8l1.Mq2.rw_cells_reshape) | autorewrite with gw_eqs; GwInst.gw_exact (@Q8l1.Mq2.rw_cells_reshape)]. Qed.

Lemma rw_cells_shape : ltac2:(Q6nq.tyx '(@Q8l1.Mq2.rw_cells_shape) [[@gw_eq_shp_sum]; [@gw_eq_shape_cells]; [@gw_eq_shp_size__3; @gw_eq_shp_size__2; @gw_eq_shp_size]] '(@nil Z) 'Q6nq.gwt_nil).
Proof. rewrite ?gw_eq_shp_sum, ?gw_eq_shape_cells; first [GwInst.gw_exact (@Q8l1.Mq2.rw_cells_shape) | autorewrite with gw_eqs; GwInst.gw_exact (@Q8l1.Mq2.rw_cells_shape)]. Qed.

Definition FILE_PAT : list shp :=
[S4; SB4; S8; S8; S8; S8; S8; S8; S8; S8; S8; S8; S8; S8; S8; S8; S4; S4; S8; S4; S4; S4; SB4; S8; S8; S8; S8; S8; S8; S8; S8; S8; S8].
Lemma gw_eq_FILE_PAT : @FILE_PAT = ltac:(GwInst.gw_term (@Q8l1.Mq2.FILE_PAT) (@FILE_PAT)). Proof. unfold FILE_PAT, Q8l1.Mq2.FILE_PAT; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_FILE_PAT : gw_eqs.

Lemma file_cells_of_junk : ltac2:(Q6nq.tyx '(@Q8l1.Mq2.file_cells_of_junk) [[@gw_eq_shp_size__3; @gw_eq_shp_size__2; @gw_eq_shp_size]; [@gw_eq_shp_sum__3; @gw_eq_shp_sum__2; @gw_eq_shp_sum]; [@gw_eq_shape_cells__3; @gw_eq_shape_cells__2; @gw_eq_shape_cells]; [@gw_eq_FILE_PAT__3; @gw_eq_FILE_PAT__2; @gw_eq_FILE_PAT]] '([232]%Z : list Z) 'Q6nq.gwt_nil).
Proof. first [GwInst.gw_exact (@Q8l1.Mq2.file_cells_of_junk) | autorewrite with gw_eqs; GwInst.gw_exact (@Q8l1.Mq2.file_cells_of_junk)]. Qed.

Lemma file_cells_zero : ltac2:(Q6nq.tyx '(@Q8l1.Mq2.file_cells_zero) [[@gw_eq_shp_size__3; @gw_eq_shp_size__2; @gw_eq_shp_size]; [@gw_eq_shp_sum__3; @gw_eq_shp_sum__2; @gw_eq_shp_sum]; [@gw_eq_shape_cells__3; @gw_eq_shape_cells__2; @gw_eq_shape_cells]; [@gw_eq_FILE_PAT__3; @gw_eq_FILE_PAT__2; @gw_eq_FILE_PAT]] '([232]%Z : list Z) 'Q6nq.gwt_nil).
Proof. first [GwInst.gw_exact (@Q8l1.Mq2.file_cells_zero) | autorewrite with gw_eqs; GwInst.gw_exact (@Q8l1.Mq2.file_cells_zero)]. Qed.
