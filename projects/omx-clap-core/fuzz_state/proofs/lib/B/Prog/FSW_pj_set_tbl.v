(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan) twin of lib/A/Prog/FSW_pj_set_tbl.v (a working branch
   f9ccbd8f565 = a working branch 6fcf9aa5a9b, blob aa73062501), the probe in the form of lib/B/FSW_parse_string_tbl.v.
   Every image value is read from image B: the range is B/YB1w.v:466 (tfib_A_pj_set = 0x83adc .. tfib_E_pj_set = 0x83ca8),
   A_pj_set is B/FSH_Base.v:61. *)
(* The decode table of pj_set in fs.asan-ubsan (image B, tfibsegs of B/YB1v.v), built over its YB1w range
   [tfib_A_pj_set, tfib_E_pj_set) = [0x83adc, 0x83ca8): 460 bytes, 115 instructions. build_table steps pc + 4: fs.asan-ubsan
   has no compressed instruction (ELF e_flags 0x4, EF_RISCV_RVC clear; MEASURED on the unstripped twin: 460 = 4 * 115, and
   capstone decodes the range as 115 four-byte instructions, the last the `jal __asan_report_store8` at 0x83ca4). The range
   holds the A code relocated by + 0x1f4 up to stage C, B's own stage D (ten UBSan checks to the trap `unimp` 0x83c84) and
   the five __asan_report_* calls 0x83c8c .. 0x83ca4. A table only (rule 24: no function proved here). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v YB1w FSH_Base.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

(* the YB1w range, in instructions *)
Definition pj_set_ninsn : nat := Z.to_nat ((tfib_E_pj_set - tfib_A_pj_set) / 4).
Lemma pj_set_range : A_pj_set = tfib_A_pj_set /\ tfib_E_pj_set - tfib_A_pj_set = 460 /\ pj_set_ninsn = 115%nat.
Proof. split; [|split]; reflexivity. Qed.

Definition pj_set_tbl : ctable := Eval vm_compute in build_table tfibsegs tfib_A_pj_set pj_set_ninsn TEmpty.
Lemma pj_set_tbl_ok : table_ok tfibsegs pj_set_tbl.
Proof.
assert (E : pj_set_tbl = build_table tfibsegs tfib_A_pj_set pj_set_ninsn TEmpty) by (vm_cast_no_check (eq_refl pj_set_tbl)).
rewrite E. apply build_table_ok0. unfold tfib_A_pj_set. lia.
Qed.
(* the first word (addi sp, sp, -0x30), the pj_get call 0x83b14, the ret 0x83b80, the UBSan trap 0x83c84 (unimp), the last
   word 0x83ca4 and nothing past the range, as image B's bytes give them (MEASURED, the unstripped twin's .text) *)
Lemma pj_set_tbl_probe :
  clookup pj_set_tbl 0x83adc = Some 0xfd010113 /\ clookup pj_set_tbl 0x83b14 = Some 0xd81ff0ef /\
  clookup pj_set_tbl 0x83b80 = Some 0x00008067 /\ clookup pj_set_tbl 0x83c84 = Some 0xc0001073 /\
  clookup pj_set_tbl 0x83ca4 = Some 0xa4dd50ef /\ clookup pj_set_tbl 0x83ca8 = None.
Proof. vm_compute. repeat split; reflexivity. Qed.
