(* fs WRITER walks, image B (fs.asan-ubsan, sha256 5ac5ce0954f8...): the decoded instruction table of the seven writer
   functions, in the donor's form (lib/B/YB1k.v: build_table over the image's own bytes, table_ok by build_table_ok0).
   The lib/B twin of lib/A/FSW_writer_tbl.v (a working branch 1a264574ee7), same names, B addresses only.
   The walks' symbolic runs (lib/B/FSW_K fsw_run_AJU / fsw_aj_runU) read instructions from it. The two ranges are
   RELOC-B's function extents (lib/B/YB1w.v tfib_A_f / tfib_E_f for each function f), each contiguous in B:
     pj_write 0x83f94, write_value 0x84010, put 0x8449c, preset_base64_encode 0x84700,
     preset_base64_decode 0x84c4c .. 0x84e70                                       = 951 words
     put_string 0x85fc8, indent 0x86368 .. 0x863d8                                  = 260 words
   (fsw_wr_extents checks both counts against YB1w's extents; YB1w is RELOC-B's, unchanged on a working branch bddf781b317).
   rule 24: proves no function (kind: segment table). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YP02.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v YB1w.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Open Scope Z_scope.

Definition FSW_WR_LO1 : Z := tfib_A_pj_write.
Definition FSW_WR_N1 : nat := 951%nat.          (* (tfib_E_preset_base64_decode - tfib_A_pj_write) / 4 *)
Definition FSW_WR_LO2 : Z := tfib_A_put_string.
Definition FSW_WR_N2 : nat := 260%nat.          (* (tfib_E_indent - tfib_A_put_string) / 4 *)

Lemma fsw_wr_extents :
  tfib_A_pj_write + 4 * Z.of_nat FSW_WR_N1 = tfib_E_preset_base64_decode /\
  tfib_A_put_string + 4 * Z.of_nat FSW_WR_N2 = tfib_E_indent.
Proof. unfold FSW_WR_N1, FSW_WR_N2. cbv. split; reflexivity. Qed.

Definition fsw_wr_tbl_build : ctable :=
  build_table tfibsegs FSW_WR_LO2 FSW_WR_N2 (build_table tfibsegs FSW_WR_LO1 FSW_WR_N1 TEmpty).
Definition fsw_wr_tbl : ctable := Eval vm_compute in fsw_wr_tbl_build.
Lemma fsw_wr_tbl_eq : fsw_wr_tbl = fsw_wr_tbl_build.
Proof. vm_cast_no_check (eq_refl fsw_wr_tbl). Qed.
Lemma fsw_wr_tbl_ok : table_ok tfibsegs fsw_wr_tbl.
Proof.
  rewrite fsw_wr_tbl_eq. unfold fsw_wr_tbl_build.
  apply build_table_ok; [cbv; discriminate|].
  apply build_table_ok0. cbv. discriminate.
Qed.

(* every entry of the seven functions is in the table: the fetch at each entry pc is the image's own word *)
Lemma fsw_wr_tbl_entries :
  Forall (fun pc => clookup fsw_wr_tbl pc <> None)
    [tfib_A_pj_write; tfib_A_write_value; tfib_A_put; tfib_A_preset_base64_encode;
     tfib_A_preset_base64_decode; tfib_A_put_string; tfib_A_indent].
Proof. vm_compute. repeat constructor; discriminate. Qed.
