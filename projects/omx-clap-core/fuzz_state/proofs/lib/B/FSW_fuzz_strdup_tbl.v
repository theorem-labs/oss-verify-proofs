(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan) twin of lib/A/FSW_fuzz_strdup_tbl.v (the canonical guarded
   table, a working branch a402e796fc1, blob ebaab1a479d), same names; B's addresses, imports point at
   lib/B's image files (YB1v, FSH_Base, FSW_K); FSH_Gen stays lib/A's, as lib/B's kit imports it.
   rule 24: proves no function (kind: segment lemma). *)
(* fuzz_strdup B 0x82d60 (fuzz/alloc.c:97-105) over fs.asan-ubsan: its decode table and the symbolic runs of its five
   straight-line stretches, checked by vm_compute. build_table steps pc + 4; fuzz_strdup has no compressed instruction.
   MEASURED (capstone 5.0.7 over the pinned fs.asan-ubsan, sha256 5ac5ce09..d204, 0x82d60..0x82db8): 92 bytes = 23
   four-byte instructions, the same words as A's fuzz_strdup (0x82ce4) except the three `jal` offsets. UBSan adds no
   check here (no arithmetic beyond strlen + 1 and no pointer adjustment). The calls: `jal __wrap_strlen` 0x82d78
   (PC_strlen 0x426c4), `jal fuzz_malloc` 0x82d84 (A_fuzz_malloc 0x82a58), `beqz a0` 0x82d8c, `jal __asan_memcpy`
   0x82d9c (PC_memcpy 0x51d90); `ret` 0x82db8. The resumed states are FSW_K's fss_ret over the four saved registers
   (sd_cs). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v FSH_Base FSW_K.
Import ListNotations.
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* ---- the code: 23 words at A_fuzz_strdup (0x82d60 .. 0x82db8), and the three return addresses ---- *)
Definition RA_SD_STRLEN : Z := 0x82d7c.   (* after `jal __wrap_strlen` 0x82d78 *)
Definition RA_SD_MALLOC : Z := 0x82d88.   (* after `jal fuzz_malloc` 0x82d84 *)
Definition RA_SD_MEMCPY : Z := 0x82da0.   (* after `jal __asan_memcpy` 0x82d9c; also the `beqz a0` target *)
Definition sd_tbl : ctable := Eval vm_compute in build_table tfibsegs A_fuzz_strdup 23 TEmpty.
Lemma sd_tbl_ok : table_ok tfibsegs sd_tbl.
Proof.
assert (E : sd_tbl = build_table tfibsegs A_fuzz_strdup 23 TEmpty) by (vm_cast_no_check (eq_refl sd_tbl)).
rewrite E. apply build_table_ok0. unfold A_fuzz_strdup. lia.
Qed.
Lemma sd_tbl_probe : clookup sd_tbl 0x82d60 = Some 0xfe010113 /\ clookup sd_tbl 0x82db8 = Some 0x00008067 /\
  clookup sd_tbl 0x82dbc = None.
Proof. vm_compute. repeat split; reflexivity. Qed.
(* the entry run stops at the strlen call with ra = 0x82d7c, sp = entry sp - 32, s0 = a0 = s *)
Example sd_run_entry :
  let r := sym_runN tfibsegs sd_tbl FUEL (fss0 A_fuzz_strdup 32) in
  ss_pc (fst r) = PC_strlen /\ sr_get (ss_regs (fst r)) 1%bv = SLit RA_SD_STRLEN /\
  sr_get (ss_regs (fst r)) 2%bv = SOff 2 (-32) /\ sr_get (ss_regs (fst r)) 8%bv = SOff 10 0 /\
  sr_get (ss_regs (fst r)) 10%bv = SOff 10 0 /\ ss_resv (fst r) = None.
Proof. vm_compute. repeat split; reflexivity. Qed.
(* the frame after any call: the four saved registers (ra, s0, s1, s2 of the entry) at sp + 24, 16, 8, 0, read back as
   the extra atoms 32 .. 35 (extra = [ra; s0; s1; s2] of the entry registers) *)
Definition sd_cs : list YP09.chunk :=
  [YP09.mkChunk 24 (CVal 8 (SOff 32 0)); YP09.mkChunk 16 (CVal 8 (SOff 33 0));
   YP09.mkChunk 8 (CVal 8 (SOff 34 0)); YP09.mkChunk 0 (CVal 8 (SOff 35 0))].
(* after strlen: s1 := a0 + 1; a0 := s1; the run stops at the fuzz_malloc call *)
Example sd_run_strlen :
  let r := sym_runN tfibsegs sd_tbl FUEL (fss_ret RA_SD_STRLEN 32 sd_cs) in
  ss_pc (fst r) = A_fuzz_malloc /\ sr_get (ss_regs (fst r)) 1%bv = SLit RA_SD_MALLOC /\
  sr_get (ss_regs (fst r)) 2%bv = SOff 2 0 /\ sr_get (ss_regs (fst r)) 8%bv = SOff 8 0 /\
  sr_get (ss_regs (fst r)) 9%bv = SOff 10 1 /\ sr_get (ss_regs (fst r)) 10%bv = SOff 10 1 /\ ss_resv (fst r) = None.
Proof. vm_compute. repeat split; reflexivity. Qed.
(* after fuzz_malloc: s2 := a0; the run stops at `beqz a0` *)
Example sd_run_malloc :
  let r := sym_runN tfibsegs sd_tbl FUEL (fss_ret RA_SD_MALLOC 32 sd_cs) in
  ss_pc (fst r) = 0x82d8c /\ snd r = RS_stopped (SR_branch BC_EQ (SOff 10 0) (SLit 0)) /\
  sr_get (ss_regs (fst r)) 18%bv = SOff 10 0.
Proof. vm_compute. repeat split; reflexivity. Qed.
(* a0 <> 0: the run stops at the memcpy call with (s2, s0, s1) *)
Example sd_run_copy :
  let r := sym_runN tfibsegs sd_tbl FUEL
    (add_cond (fst (sym_runN tfibsegs sd_tbl FUEL (fss_ret RA_SD_MALLOC 32 sd_cs))) (mkAC BC_NE (SOff 10 0) (SLit 0))) in
  ss_pc (fst r) = PC_memcpy /\ sr_get (ss_regs (fst r)) 1%bv = SLit RA_SD_MEMCPY /\
  sr_get (ss_regs (fst r)) 10%bv = SOff 10 0 /\ sr_get (ss_regs (fst r)) 11%bv = SOff 8 0 /\
  sr_get (ss_regs (fst r)) 12%bv = SOff 9 0 /\ sr_get (ss_regs (fst r)) 2%bv = SOff 2 0 /\ ss_resv (fst r) = None.
Proof. vm_compute. repeat split; reflexivity. Qed.
(* a0 = 0: the epilogue stops at `ret` with a0 = 0 *)
Example sd_run_null :
  let r := sym_runN tfibsegs sd_tbl FUEL
    (add_cond (fst (sym_runN tfibsegs sd_tbl FUEL (fss_ret RA_SD_MALLOC 32 sd_cs))) (mkAC BC_EQ (SOff 10 0) (SLit 0))) in
  ss_pc (fst r) = 0x82db8 /\ snd r = RS_stopped (SR_jalr (SOff 32 0)) /\ sr_get (ss_regs (fst r)) 10%bv = SOff 10 0 /\
  sr_get (ss_regs (fst r)) 2%bv = SOff 2 32.
Proof. vm_compute. repeat split; reflexivity. Qed.
(* after memcpy: the epilogue stops at `ret` with a0 = s2 *)
Example sd_run_ret :
  let r := sym_runN tfibsegs sd_tbl FUEL (fss_ret RA_SD_MEMCPY 32 sd_cs) in
  ss_pc (fst r) = 0x82db8 /\ snd r = RS_stopped (SR_jalr (SOff 32 0)) /\ sr_get (ss_regs (fst r)) 10%bv = SOff 18 0 /\
  sr_get (ss_regs (fst r)) 8%bv = SOff 33 0 /\ sr_get (ss_regs (fst r)) 9%bv = SOff 34 0 /\
  sr_get (ss_regs (fst r)) 18%bv = SOff 35 0 /\ sr_get (ss_regs (fst r)) 2%bv = SOff 2 32.
Proof. vm_compute. repeat split; reflexivity. Qed.
