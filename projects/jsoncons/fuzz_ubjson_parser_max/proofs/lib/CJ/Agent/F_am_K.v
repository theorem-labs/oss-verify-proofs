(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_syscalls MallocRep F_malloc_free MallocTree.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import MallocKit_B MallocModel_B MallocKit_B3 F_ntf_B.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Agent_F_am_K () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_syscalls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Cells."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Step."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "1cons"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "2eq"; "3Z"; "4asegs"; "5meta_cells"; "5wz"; "5zeros"; "6C4"; "6C8"; "6cell"]; ["6cells_bytes"; "6cells_size"; "6cells_wf"; "7bytes_at"; "7le4"; "7le8"; "7wr_at"; "8rw_cells"; "9meta0"; "9mstate"; ":add"; ":le"; ":of_nat"; "0cs"; "0k"; "0m"]; ["0n"; "0off"; "0st"; ";bv"]]).
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Lemma zeros_length : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_am_K "<'4'7&2'Q3y8%211&<r1%211%7241%93:13pR2;1"). Proof. intros n. unfold zeros. apply repeat_length. Qed.
Lemma bytes_at_zeros_sub : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_am_K "Q8'Q3yR0%211'6y8%511%311p051'8'4&C&9r5r4&<r3%211%746541&Kz%2215&J&L%118%32;1%31=%8221r8r7%821A%@1A%E4D421p061p0=1p0A1pQNJ1pR4L1pR2L1p2N1pR0Q01").
Proof. intros m A n off k.
intros (H0 & H1 & HB) Hoff Hk. rewrite zeros_length in H1, HB. split; [lia|]. rewrite zeros_length. split; [lia|].
intros i Hi. replace (A + off + Z.of_nat i) with (A + Z.of_nat (Z.to_nat off + i)) by lia.
rewrite HB by lia. unfold zeros. rewrite !nth_error_repeat by lia. reflexivity.
Qed.
Lemma rw_cells_of_zeros : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_am_K "QO'Q3yR0%211'6y8%511%311p051'8'4'3'?%211&C&9r5r4&<r3%211%746541&Fr6&L%118%44;3:1&B%119'7%C1H&@%11?&A%11A%A11%73641&Kz%221@&Jr7%91C%C11%4231r8%F11%:231&Gr;r:%;216%44Q531;p061p0?1p0C1p0L1p0O1p0Q51pQLQ>1pR4QC1pR2QC1p2QE1pR0QG1").
Proof. intros m A n off cs.
intros HB HW WF E Hoff Hsz. apply rw_cells_of_bytes; [exact WF| |].
- rewrite E. apply (bytes_at_zeros_sub m A n off); assumption.
- eapply wr_at_sub; [exact HW| lia| lia].
Qed.
Lemma le8_zero : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_am_K "?'7'3'Q3y8%211%411&E&;z%211%411&<u8%211%>3941"). Proof. reflexivity. Qed.
Lemma le4_zero : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_am_K "?'7'3'Q3y8%211%411&D&;z%211%411&<u4%211%>3941"). Proof. reflexivity. Qed.
Lemma meta_cells_meta0 : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_am_K "K'I'7'3'?%211&:r1&H%3221(1(>&;z%211%411(=%113(5%11?%:3@51%;3A41%<3B51%=3C81%>3D91%?3E:1%H3EA1pR6J1").
Proof. intros st. reflexivity. Qed.
Definition carve_st (st : mstate) (p : aptr) : mstate :=
let st1 := upd_ctx (fun c => set_avail_meta_areas (Some (aadd p 4096)) (set_avail_meta_area_count (c_avail_meta_area_count c - 1) c)) st in
let st2 := match c_meta_area_tail (ctx st1) with
| Some tl => set_areas (<[tl := match (s_areas st1) !! tl with
| Some a => mkArea (a_check a) (Some p) (a_nslots a)
| None => mkArea 0 (Some p) 0 end]> (s_areas st1)) st1
| None => upd_ctx (set_meta_area_head (Some p)) st1
end in
let st3 := upd_ctx (set_meta_area_tail (Some p)) st2 in
let old := default (mkArea 0 None 0) ((s_areas st3) !! p) in
set_areas (<[p := mkArea (c_secret (ctx st3)) (a_next old) NSLOTS]> (s_areas st3)) st3.
Lemma am_carve_eq {R} st p (k : mstate -> optr -> M R) bail :
am_carve st p k bail = am_take (upd_ctx (fun c => set_avail_meta (Some (aadd p AREA_HDR)) (set_avail_meta_count NSLOTS c)) (carve_st st p)) k bail.
Proof. reflexivity. Qed.
End CEIL_WRAP_1.
