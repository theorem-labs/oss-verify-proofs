(* fs program part, lane CHECKS, image B (fs.asan-ubsan): the decode table of check_reject_clean's own text, for the
   walk's symbolic runs (lib/B/FSW_K.v fsw_run_AJU takes `table_ok tfibsegs tbl`). The range is lib/B/YB1w.v's names:
   tfib_A_check_reject_clean = 0x81b5c .. tfib_E_check_reject_clean = 0x81b9c, 64 bytes. build_table steps pc + 4
   (Reusable/YP02.v), so the count is in 32-bit words: 16. MEASURED on the pinned fs.asan-ubsan (sha256 5ac5ce09...):
   those 64 bytes decode to exactly 16 instructions, each 4 bytes (capstone, RISCV64 + C): the 15 words of the A twin's
   shape and a trailing `unimp` (0xc0001073) at 0x81b98, which no path reaches. Its one call (`jal fuzz_alloc_live` at
   0x81b78) leaves the range: lib/B/FSW_fuzz_alloc_live_tbl.v holds the callee's words. Twin of
   lib/A/FSW_check_reject_clean_tbl.v (a working branch 3694074f8f1). *)
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

Definition crc_text_start : Z := tfib_A_check_reject_clean.
Definition crc_text_count : nat := Z.to_nat ((tfib_E_check_reject_clean - tfib_A_check_reject_clean) / 4).
(* the range is a whole number of words, so the table covers it exactly *)
Lemma crc_text_exact : Z.of_nat crc_text_count * 4 = tfib_E_check_reject_clean - tfib_A_check_reject_clean.
Proof. vm_compute. reflexivity. Qed.

Definition crc_tbl : ctable := Eval vm_compute in (build_table tfibsegs crc_text_start crc_text_count TEmpty).
Lemma crc_tbl_eq : crc_tbl = build_table tfibsegs crc_text_start crc_text_count TEmpty.
Proof. vm_cast_no_check (eq_refl crc_tbl). Qed.
Lemma crc_tbl_ok : table_ok tfibsegs crc_tbl.
Proof. rewrite crc_tbl_eq. apply build_table_ok0. cbv. discriminate. Qed.
