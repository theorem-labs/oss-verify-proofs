(* fs WRITER walks: the decoded instruction table of the seven writer functions of fs.asan, in the donor's form
   (lib/A/AB1k.v: build_table over the image's own bytes, table_ok by build_table_ok0). The walks' symbolic runs
   (FSW_K fsw_run_AJU / fsw_aj_runU) read instructions from it. The two ranges are RELOC's function extents
   (lib/A/AB1w.v:468-479):
     pj_write 0x83d08, write_value 0x83d84, put 0x8418c, preset_base64_encode 0x84390,
     preset_base64_decode 0x8481c .. 0x84a04                                       = 831 words
     put_string 0x85ad8, indent 0x85e4c .. 0x85ebc                                  = 249 words
   Rule 24 (proof-index v5 built 2026-10-28T21:58:24Z, exit 0, read from a file, not a pipe): put, indent,
   put_string, write_value, pj_write, preset_base64_encode and preset_base64_decode have RELEASED proofs for fs's
   PLAIN and UBSAN builds only (lib/Prog, lib/U/Prog, ossv/recipes@566eb6ffa5, release/pau-projects-recipes@b6a0088adc),
   none for an ASan build. Those plain contracts / proofs are the templates used here, not drop-ins.
   The released plain tables are over fs.plain's addresses; this table is fs.asan's. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YP02.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1v AB1w.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Open Scope Z_scope.

Definition FSW_WR_LO1 : Z := tfib_A_pj_write.
Definition FSW_WR_N1 : nat := 831%nat.          (* (tfib_E_preset_base64_decode - tfib_A_pj_write) / 4 *)
Definition FSW_WR_LO2 : Z := tfib_A_put_string.
Definition FSW_WR_N2 : nat := 249%nat.          (* (tfib_E_indent - tfib_A_put_string) / 4 *)

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
