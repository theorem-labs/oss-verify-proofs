(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_memcpy_A F_memcpy.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_syscalls MallocRep F_malloc_free MallocTree.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import MallocKit_B MallocModel_B MallocKit_B3 F_ntf_B.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_am_A F_am_K.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Agent_F_am_E () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_syscalls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Arr."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Cells."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Step."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "1Some"; "1app"; "1list"; "1option"; "2and"; "2eq"; "3Z"; "4ov_read_bytes"; "5asegs"; "6u64s"; "7cell"; "7cells_size"; "8bytes_at"; "8le8"; "8wa"]; ["9rw_cells"; ":nth_error"; ";add"; ";le"; ";mul"; ";of_nat"; ";to_nat"; "0a"; "0cs1"; "0cs2"; "0i"; "0m"; "<bv"; "0w"; "0ws"]]).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac showregs := lazymatch goal with |- evt _ _ (MS ?R _ ?pc _ _ ?m _) => idtac "REGS" R "PC" pc "MEM" m end.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Lemma u64s_read : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_am_E "QM'LyR0%211'4y8%511%311p051'7'3%118&=&9r6r5&:r4%211%746541'6%A1B&A&F%117%33F:1(1r3%22I1%93841&Cz%221A&?&Br8&D+8%221H%5241%711%E3Q6H1%Q01Q4%Q711&8r:u8%34Q22Q01&>%11Q3%H281%O3841p0;1p0E1p0I1p0Q41pQ@QE1pQLQF1pQFQA1pQNQ@1p2QC1pQHQE1").
Proof.
intros m A ws i w a HB Hn Hi Ha.
pose proof (bytes_at_bound _ _ _ _ HB) as B.
apply (u64arr_read asegs m A ws i w a); try assumption. split; [exact HB|].
Abort.
Lemma u64s_read : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_am_E "QM'LyR0%211'4y8%511%311p051'7'3%118&=&9r6r5&:r4%211%746541'6%A1B&A&F%117%33F:1(1r3%22I1%93841&Cz%221A&?&Br8&D+8%221H%5241%711%E3Q6H1%Q01Q4%Q711&8r:u8%34Q22Q01&>%11Q3%H281%O3841p0;1p0E1p0I1p0Q41pQ@QE1pQLQF1pQFQA1pQNQ@1p2QC1pQHQE1").
Proof.
intros m A ws i w a Hb Hn Hi ->.
destruct (u64s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
replace (8 * i)%Z with (Z.of_nat (8 * Z.to_nat i))%Z by lia.
rewrite (bytes_at_ov_read asegs m A (u64s ws) (8 * Z.to_nat i) 8 Hb).
2:{ rewrite Eu, !app_length, length_le8, Hlu. lia. }
rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
rewrite firstn_app, firstn_all2 by (rewrite length_le8; lia).
rewrite length_le8, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
Qed.
Lemma rw_cells_app_split : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_am_E "Q5'LyR0%211'4y8%511%311p051'7'3';%211&@&9r4r3&2r2r1%33921%847651'5r5%;4:198&B&E&<%11<%311%52?1%B4A81=%:281p0<1pQDF1pQBG1p2K1pQHM1").
Proof.
intros m A cs1 cs2 H. split; [eapply rw_cells_prefix; exact H|].
destruct H as [[WF B] W].
apply cells_wf_app in WF. destruct WF as [WF1 WF2].
rewrite cells_bytes_app in B. apply bytes_at_app in B. destruct B as [_ B2]. rewrite cells_bytes_length in B2 by exact WF1.
split; [split; [exact WF2 | exact B2] |].
rewrite cells_size_app in W. eapply wr_at_sub; [exact W | lia | lia].
Qed.
Lemma rw_cells_app_join : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_am_E "Q4'LyR0%211'4y8%511%311p051'7'3';%211&@&9r4r3r2%544321r5&B&E&<%117%311%52:1%=4<719r6&2%13B>=%A4@3;1p051p0>1pQDE1pQBF1p2J1pQHL1").
Proof.
intros m A cs1 cs2 [[WF1 B1] W1] [[WF2 B2] W2]. split; [split|].
- apply cells_wf_app. split; assumption.
- rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|]. rewrite cells_bytes_length by exact WF1. exact B2.
- rewrite cells_size_app. destruct W1 as (H0 & H1 & X1). destruct W2 as (H2 & H3 & X2). split; [lia|]. split; [lia|].
intros i Hi. destruct (Z.lt_ge_cases i (Z.of_nat (cells_size cs1))).
+ apply X1. lia.
+ replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia. apply X2. lia.
Qed.
Definition am_init_st (st : mstate) : mstate :=
if c_init_done (ctx st) =? 0 then upd_ctx (fun c => set_init_done 1 (set_secret (s_secret st) c)) st else st.
End CEIL_WRAP_1.
