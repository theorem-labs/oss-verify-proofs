(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg L5Defs L5Core FrmInv. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import DecIface_u5 DecJson_u5.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module PSI.
Definition WIN : Z := 8672.        (* [comment removed for export] *)
Definition CSAVED : list nat := [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Section Contracts.
Variable segs : list Segment.
Context {SCFG_P : ScfgP}.
Variable A : PDC.addrs.
Definition floatscan_contract (pc : Z) : Prop :=
  forall (fx : FPState) R M model K sp F s CAN txt,
  m_halted model = None -> m_vm_lazy model = [] -> FrmInv.fp_ok fx ->
  PDC.rz R 2 = sp -> sp mod 16 = 0 -> PDC.STK_FLOOR + WIN <= sp <= 2 ^ 47 -> L5.defined M (sp - WIN) WIN ->
  PDC.rz R 10 = F -> PDC.rz R 11 = 1 -> PDC.rz R 12 = 1 -> PDC.rz R 4 = PDC.a_TP A -> Hoare.ret_ok (getr R (PDC.reg_of 1)) ->
  PDC.file_ok segs M F s -> PDC.apart (F + 8) 192 (sp - WIN) WIN ->
  L5.u64_at segs M (PDC.a_G A) CAN -> PDC.apart (PDC.a_G A) 8 (sp - WIN) WIN ->
  PDC.text_ok segs M s txt -> PDC.text_apart A s txt F (sp - WIN) WIN -> PDJ.num_final txt ->
  L5.writable segs M (PDC.a_TP A - 164) 4 -> L5.img_clear M (PDC.a_img_lo A) (PDC.a_img_hi A) ->
  (forall (fx' : FPState) R' M', FrmInv.fp_ok fx' ->
      (forall x : nat, In x CSAVED -> getr R' (PDC.reg_of x) = getr R (PDC.reg_of x)) ->
      (forall a : word, ~ (sp - WIN <= bv_unsigned a < sp) -> ~ (F + 8 <= bv_unsigned a < F + 16) -> ~ (PDC.a_TP A - 164 <= bv_unsigned a < PDC.a_TP A - 160) -> M' a = M a) ->
      mem_grows M M' ->
      L5.u64_at segs M' (F + 8) (s + Z.of_nat (length txt)) ->
      srealizes segs SCFG (mkCfg (@mkst fx' R' (getr R (PDC.reg_of 1)) M' (seg_rom segs)) model) K) ->
  srealizes segs SCFG (mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom segs)) model) K.
End Contracts.
End PSI.
