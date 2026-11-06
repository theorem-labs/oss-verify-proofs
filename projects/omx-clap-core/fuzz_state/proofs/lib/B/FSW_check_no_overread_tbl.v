(* fs program part, lane CNO, image B (fs.asan-ubsan): the decode table of check_no_overread's own text (B 0x8124c,
   972 bytes), for the walk's symbolic runs (B FSW_K.v fsw_run_AJU / fsw_run_to_AJU / the token runs take
   `table_ok tfibsegs tbl`). build_table steps pc + 4 (Reusable/YP02.v:19-22), so the count is in 32-bit words: 243.
   MEASURED on the pinned fs.asan-ubsan (neutral_dis listing
   (internal path)): 0x8124c .. 0x81614 is 243
   instructions, each a 32-bit word (0x81618 - 0x8124c = 972 = 4 * 243), so the function has no compressed
   instruction and every instruction it executes is a table entry; its calls leave the range.
   Template (text only): lib/A/FSW_check_no_overread_tbl.v at a working branch 59f0008819f. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YP02.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v FSH_Base.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

Definition cno_tbl : ctable := Eval vm_compute in build_table tfibsegs A_check_no_overread 243 TEmpty.
Lemma cno_tbl_eq : cno_tbl = build_table tfibsegs A_check_no_overread 243 TEmpty.
Proof. vm_cast_no_check (eq_refl cno_tbl). Qed.
Lemma cno_tbl_ok : table_ok tfibsegs cno_tbl.
Proof. rewrite cno_tbl_eq. apply build_table_ok0. unfold A_check_no_overread. lia. Qed.
