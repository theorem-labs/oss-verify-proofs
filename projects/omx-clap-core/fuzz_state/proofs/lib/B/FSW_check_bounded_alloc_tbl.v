(* fs program part, lane CHECKS, image B (fs.asan-ubsan): the decode table of check_bounded_alloc's own text, for the
   walk's symbolic runs (lib/B/FSW_K.v fsw_run_AJU takes `table_ok tfibsegs tbl`). The range is lib/B/YB1w.v's names:
   tfib_A_check_bounded_alloc = 0x81618 .. tfib_E_check_bounded_alloc = 0x8164c, 52 bytes. build_table steps pc + 4
   (Reusable/YP02.v), so the count is in 32-bit words: 13. MEASURED on the pinned fs.asan-ubsan (sha256 5ac5ce09...):
   those 52 bytes decode to exactly 13 instructions, each 4 bytes (capstone, RISCV64 + C): the 12 words of the A twin's
   shape and a trailing `unimp` (0xc0001073) at 0x81648, which no path reaches. Twin of lib/A/FSW_check_bounded_alloc_tbl.v
   (a working branch 3694074f8f1). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1a YK1e.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v YB1w.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Open Scope Z_scope.

Definition cba_text_start : Z := tfib_A_check_bounded_alloc.
Definition cba_text_count : nat := Z.to_nat ((tfib_E_check_bounded_alloc - tfib_A_check_bounded_alloc) / 4).
(* the range is a whole number of words, so the table covers it exactly *)
Lemma cba_text_exact : Z.of_nat cba_text_count * 4 = tfib_E_check_bounded_alloc - tfib_A_check_bounded_alloc.
Proof. vm_compute. reflexivity. Qed.

Definition cba_tbl : ctable := Eval vm_compute in (build_table tfibsegs cba_text_start cba_text_count TEmpty).
Lemma cba_tbl_eq : cba_tbl = build_table tfibsegs cba_text_start cba_text_count TEmpty.
Proof. vm_cast_no_check (eq_refl cba_tbl). Qed.
Lemma cba_tbl_ok : table_ok tfibsegs cba_tbl.
Proof. rewrite cba_tbl_eq. apply build_table_ok0. cbv. discriminate. Qed.
