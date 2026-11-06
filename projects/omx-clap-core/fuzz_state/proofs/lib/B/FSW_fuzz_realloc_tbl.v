(* The decode table of fuzz_realloc in fuzz_state.asan-ubsan (image B: A_fuzz_realloc = 0x82bc4 .. 0x82d60, st_size 412 =
   103 words), for the symbolic engine's runs in lib/B/FSW_realloc*.v. build_table steps pc + 4, valid because the
   function has no compressed (RVC) instruction: every one of its 103 instructions is 4 bytes (MEASURED: capstone 5.0.7
   on the unstripped twin of the pinned fuzz_state.asan-ubsan, sha256 5ac5ce09...).
   proves function fuzz_realloc (B 0x82bc4) (reuse search: proof-index on main@f4cc67298b7 / ossv/recipes@5121fb8693b
   / ossv/candidates@ee89628c997 / release/pau-projects-recipes@b6a0088adcb, by address on those four refs, and on named
   lane branches / `proof-index fuzz_realloc`, `git grep -i -e <addr>`, `git grep -E '^(Theorem|Lemma)
   .*fuzz_realloc_spec'`; B 0x82bc4: 0 hits, CONFIRM).
   Port-from: lib/A/FSW_fuzz_realloc_tbl.v (this lane's A table), lib/B/FSW_own.v's tbl_own. No rename. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1a YK1e.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v FSH_Base.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.
Definition fsr_text_count : nat := 103.
Definition fsr_tbl : ctable := Eval vm_compute in (build_table tfibsegs A_fuzz_realloc fsr_text_count TEmpty).
Lemma fsr_tbl_eq : fsr_tbl = build_table tfibsegs A_fuzz_realloc fsr_text_count TEmpty.
Proof. vm_cast_no_check (eq_refl fsr_tbl). Qed.
Lemma fsr_tbl_ok : table_ok tfibsegs fsr_tbl.
Proof. rewrite fsr_tbl_eq. apply build_table_ok0. unfold A_fuzz_realloc. lia. Qed.
