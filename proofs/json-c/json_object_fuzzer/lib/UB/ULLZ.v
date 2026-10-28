(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply GwApply2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q0Hd.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UC8c.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UC8c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UC8c.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q8tj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8tj.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSL3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSL3.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr.
Open Scope Z_scope.


Definition new_slot (k v pad pv : Z) : slotv := SV k 0 pad v 0 pv.
Definition ins_svs (svs : list slotv) (g : nat) (sg : slotv) (k v : Z) (hd tl : Z) (ixl : nat) (sl : slotv) (tbl : Z) : list slotv :=
if hd =? 0 then upd svs g (new_slot k v (sv_pad sg) 0)
else upd (upd svs g (new_slot k v (sv_pad sg) tl)) ixl (SV (sv_k sl) (sv_kc sl) (sv_pad sl) (sv_v sl) (ent_addr tbl g) (sv_pv sl)).

Section LhStore.
Variables (sp gp tp : word) (s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (t tbl size k v : Z) (svs : list slotv) (ffn : Z).
Variables (rac s0c s1c s2c s3c s4c s5c : word).

Definition ins_frame (m : word -> option byte) (junk8 : list byte) : Prop :=
rw_cells rsegs m (bv_unsigned sp + -64) [CB 8 junk8; C8 s5c; C8 s4c; C8 s3c; C8 s2c; C8 s1c; C8 s0c; C8 rac].

Definition hdr_cells (sz cnt hd tl : Z) : list cell :=
[C4 (Z_to_bv 64 sz); C4 (Z_to_bv 64 cnt); C8 (Z_to_bv 64 hd); C8 (Z_to_bv 64 tl); C8 (Z_to_bv 64 tbl);
C8 (Z_to_bv 64 ffn); C8 (Z_to_bv 64 (fn_lh_char_hash S4F)); C8 (Z_to_bv 64 (fn_lh_char_equal S4F))].

End LhStore.
