(* The decode table of fuzz_realloc in fuzz_state.asan (A_fuzz_realloc 0x829e8 .. 0x82ce4: 191 instructions, 764
   bytes), for the symbolic engine's runs in lib/A/FSW_realloc.v. build_table steps pc + 4, which is valid because the
   function has no compressed (RVC) instruction: every one of its 191 instructions is 4 bytes and 4 x 191 = 764 is its
   byte size (measured by decoding the unstripped twin of the pinned fuzz_state.asan, sha256 64b53ff8...: capstone
   5.0.7, and the integrator's check of all ALLOC functions, owner 21:5xZ).
   Port-from: lib/A/AB1k.v (the donor's per-range table: build_table, its _eq by vm_cast_no_check, table_ok by
   build_table_ok0). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1a YK1e.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK0c YK0e YK0f YK09 YA0c YA0e YA0f.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.
Definition fsr_text_start : Z := 0x829e8.
Definition fsr_text_count : nat := 191.
Definition fsr_tbl : ctable := Eval vm_compute in (build_table tfibsegs fsr_text_start fsr_text_count TEmpty).
Lemma fsr_tbl_eq : fsr_tbl = build_table tfibsegs fsr_text_start fsr_text_count TEmpty.
Proof. vm_cast_no_check (eq_refl fsr_tbl). Qed.
Lemma fsr_tbl_ok : table_ok tfibsegs fsr_tbl.
Proof. rewrite fsr_tbl_eq. apply build_table_ok0. cbv. discriminate. Qed.
