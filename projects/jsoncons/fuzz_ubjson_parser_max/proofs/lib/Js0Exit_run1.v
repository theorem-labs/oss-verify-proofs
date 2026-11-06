(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic Js0ExitBase.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Export Js0AtexitCells.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Js0Exit_run1 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0Exit_run1.FPX_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1Some"; "1bool"; "1cons"; "1list"; "1nil"; "1option"; "1true"; "2I"; "2and"; "2eq"; "2ex"; "3store_ok"; "3word_to_le_bytes"; "4bvmap"; "5msteps"; "6mem_w2"]; ["7getr"; "7mkst"; "7rdn"; "8loaded_segments"; "9le"; "9sub"; "0code"; "0fx"; "0mem"; "0regs"; "0regs'"; "0rom"; "0s1v"; "0sp"; ":BV"; ":Z_to_bv"]; [":bv"; ":bv_unsigned"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPX_1. Context {fx : PropExec.FPState}.
Definition ax_writes (n : nat) (m : word -> option byte) : word -> option byte :=
match n with
| O => m
| S O => wbytes (wbytes (wbytes (wbytes m
(Z_to_bv 64 0xe7cb0) (word_to_le_bytes 4 (Z_to_bv 64 0)))
(Z_to_bv 64 0xe7cb0) (word_to_le_bytes 4 (Z_to_bv 64 18446744073709551615)))
(Z_to_bv 64 0xe7cb0) (word_to_le_bytes 4 (Z_to_bv 64 32)))
(Z_to_bv 64 0xe7cb8) (word_to_le_bytes 8 (Z_to_bv 64 0))
| S (S _) => wbytes (wbytes (wbytes (wbytes (wbytes m
(Z_to_bv 64 0xe7cb0) (word_to_le_bytes 4 (Z_to_bv 64 1)))
(Z_to_bv 64 0xe7cb0) (word_to_le_bytes 4 (Z_to_bv 64 0)))
(Z_to_bv 64 0xe7cb0) (word_to_le_bytes 4 (Z_to_bv 64 18446744073709551615)))
(Z_to_bv 64 0xe7cb0) (word_to_le_bytes 4 (Z_to_bv 64 32)))
(Z_to_bv 64 0xe7cb8) (word_to_le_bytes 8 (Z_to_bv 64 0))
end.
Definition mem_w1 (n : nat) (mem : word -> option byte) (sp ra s0 : word) (tid : Z) (code s1 s2 s3 : word) :=
wbytes (ax_writes n (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
(Z_to_bv 64 (bv_unsigned sp - 8)) (word_to_le_bytes 8 ra))
(Z_to_bv 64 (bv_unsigned sp - 16)) (word_to_le_bytes 8 s0))
(Z_to_bv 64 0xe7ec8) (word_to_le_bytes 4 (Z_to_bv 64 tid)))
(Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x98b34)))
(Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
(Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 s1))
(Z_to_bv 64 (bv_unsigned sp - 48)) (word_to_le_bytes 8 s2))
(Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 s3)))
(Z_to_bv 64 0xe7ca8) [Z_to_bv 8 1].
Lemma w1 : forall (n : nat) regs mem rom (sp tp code : word) (tid : Z),
getr regs 2 = sp -> getr regs 4 = tp -> getr regs 10 = code ->
(4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
(168 <= bv_unsigned tp)%Z -> (bv_unsigned tp <= 4294967296)%Z ->
(0 < tid < 2147483648)%Z ->
rdn RSEGS mem (Z_to_bv 64 (bv_unsigned tp - 168)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) ->
rdn RSEGS mem (Z_to_bv 64 0xe7ec8) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
stdio_globals mem ->
atexit_cells mem n ->
exists regs',
msteps RSEGS (mkst regs (0x98ad0 : word) mem rom)
(mkst regs' (0x98a84 : word) (mem_w1 n mem sp (getr regs 1) (getr regs 8) tid code (getr regs 9) (getr regs 18) (getr regs 19)) rom)
/\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
/\ getr regs' 8 = code
/\ getr regs' 1 = Z_to_bv 64 0x98b38
/\ getr regs' 4 = tp /\ getr regs' 3 = getr regs 3 /\ getr regs' 9 = getr regs 9.
Proof.
intros n regs mem rom sp tp code tid Hsp Htp Ha0 SPlo SPhi SOK TPlo TPhi TID Mtid Mlock GL AX.
destruct GL as (Gnl & _).
destruct n as [|[|k]].
{
destruct AX as (Mxl & Mxh). unfold mem_w1, ax_writes. eexists. split.
-
stepn (ltac:(oF' 0x98ad0%Z)) (ltac:(oD' 0x98ad0%Z)). rewrite Hsp. sp_renorm.
stepST (ltac:(oF' 0x98ad4%Z)) (ltac:(oD' 0x98ad4%Z)) (Z_to_bv 64 (bv_unsigned sp - 8)) (getr regs 1) ltac:(sok_stack SOK).
stepST (ltac:(oF' 0x98ad8%Z)) (ltac:(oD' 0x98ad8%Z)) (Z_to_bv 64 (bv_unsigned sp - 16)) (getr regs 8) ltac:(sok_stack SOK).
stepn (ltac:(oF' 0x98adc%Z)) (ltac:(oD' 0x98adc%Z)).
stepn (ltac:(oF' 0x98ae0%Z)) (ltac:(oD' 0x98ae0%Z)). rewrite Htp.
stepLD (ltac:(oF' 0x98ae4%Z)) (ltac:(oD' 0x98ae4%Z)) (word_to_le_bytes 4 (Z_to_bv 64 tid)) (Z_to_bv 64 tid)
ltac:(change (v_addi tp (-168)) with (Z_to_bv 64 (bv_unsigned tp - 168)); rdn_by Mtid)
ltac:(apply bytes_le_to_Z_4; u_norm; lia).
rewrite (v_lw_small tid) by lia.
stepn (ltac:(oF' 0x98ae8%Z)) (ltac:(oD' 0x98ae8%Z)).
stepn (ltac:(oF' 0x98aec%Z)) (ltac:(oD' 0x98aec%Z)).
eapply mst_step; [reflexivity
| eapply step_lr_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
[ exact (ltac:(oF' 0x98af0%Z)) | reflexivity | exact (ltac:(oD' 0x98af0%Z))
| gres; u_norm; reflexivity
| gres; rdn_by Mlock
| apply bytes_le_to_Z_4; u_norm; lia ]
| ].
reduce_bv_eqb_ifs; norm_pc_r; vnorm.
eapply mst_step; [reflexivity
| eapply step_bne_ft_r; [exact (ltac:(oF' 0x98af4%Z)) | reflexivity | exact (ltac:(oD' 0x98af4%Z)) | gres; cond_compute ] | ].
norm_pc_r.
eapply mst_step; [reflexivity
| eapply step_sc_w_ok; [exact (ltac:(oF' 0x98af8%Z)) | reflexivity | exact (ltac:(oD' 0x98af8%Z))
| gres; u_norm; reflexivity | gres; reflexivity | gres; sok_data ] | ].
step_simpl; vnorm.
stepb_ft (ltac:(oF' 0x98afc%Z)) (ltac:(oD' 0x98afc%Z)) ltac:(cond_compute).
stepn (ltac:(oF' 0x98b00%Z)) (ltac:(oD' 0x98b00%Z)).
stepb_ft (ltac:(oF' 0x98b04%Z)) (ltac:(oD' 0x98b04%Z)) ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; u_norm; lia).
stepb_tk (ltac:(oF' 0x98b08%Z)) (ltac:(oD' 0x98b08%Z)) ltac:(cond_compute).
stepn (ltac:(oF' 0x98b2c%Z)) (ltac:(oD' 0x98b2c%Z)). rewrite Ha0.
stepn (ltac:(oF' 0x98b30%Z)) (ltac:(oD' 0x98b30%Z)).
stepn (ltac:(oF' 0x98824%Z)) (ltac:(oD' 0x98824%Z)). sp_renorm.
stepST (ltac:(oF' 0x98828%Z)) (ltac:(oD' 0x98828%Z)) (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x98b34) ltac:(sok_stack SOK).
stepST (ltac:(oF' 0x9882c%Z)) (ltac:(oD' 0x9882c%Z)) (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
stepST (ltac:(oF' 0x98830%Z)) (ltac:(oD' 0x98830%Z)) (Z_to_bv 64 (bv_unsigned sp - 40)) (getr regs 9) ltac:(sok_stack SOK).
stepST (ltac:(oF' 0x98834%Z)) (ltac:(oD' 0x98834%Z)) (Z_to_bv 64 (bv_unsigned sp - 48)) (getr regs 18) ltac:(sok_stack SOK).
stepST (ltac:(oF' 0x98838%Z)) (ltac:(oD' 0x98838%Z)) (Z_to_bv 64 (bv_unsigned sp - 56)) (getr regs 19) ltac:(sok_stack SOK).
stepn (ltac:(oF' 0x9883c%Z)) (ltac:(oD' 0x9883c%Z)). stepn (ltac:(oF' 0x98840%Z)) (ltac:(oD' 0x98840%Z)). stepn (ltac:(oF' 0x98844%Z)) (ltac:(oD' 0x98844%Z)). stepn (ltac:(oF' 0x98848%Z)) (ltac:(oD' 0x98848%Z)).
stepn (ltac:(oF' 0x9884c%Z)) (ltac:(oD' 0x9884c%Z)).
stepn (ltac:(oF' 0xa9df0%Z)) (ltac:(oD' 0xa9df0%Z)).
chain_step; [reflexivity
| eapply step_lb with (b := Z_to_bv 8 0);
[exact (ltac:(oF' 0xa9df4%Z)) | reflexivity | exact (ltac:(oD' 0xa9df4%Z)) | gres; imm_norm; addr_norm; rdn_by Gnl]
| step_simpl]; vnorm.
stepb_tk (ltac:(oF' 0xa9df8%Z)) (ltac:(oD' 0xa9df8%Z)) ltac:(cond_compute).
stepret (ltac:(oF' 0xa9fe8%Z)) (ltac:(oD' 0xa9fe8%Z)) (0x98850 : word) ltac:(bveq).
stepLD (ltac:(oF' 0x98850%Z)) (ltac:(oD' 0x98850%Z)) (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_by Mxh) ltac:(apply bytes_le_to_Z_8).
stepb_tk (ltac:(oF' 0x98854%Z)) (ltac:(oD' 0x98854%Z)) ltac:(cond_compute).
stepn (ltac:(oF' 0x988c4%Z)) (ltac:(oD' 0x988c4%Z)).
stepST (ltac:(oF' 0x988c8%Z)) (ltac:(oD' 0x988c8%Z)) (Z_to_bv 64 0xe7ca8) (Z_to_bv 64 1) ltac:(sok_data).
change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
stepn (ltac:(oF' 0x988cc%Z)) (ltac:(oD' 0x988cc%Z)).
stepLD8 (ltac:(oF' 0x988d0%Z)) (ltac:(oD' 0x988d0%Z)) (Z_to_bv 64 0x98b34).
stepLD8 (ltac:(oF' 0x988d4%Z)) (ltac:(oD' 0x988d4%Z)) code.
stepLD8 (ltac:(oF' 0x988d8%Z)) (ltac:(oD' 0x988d8%Z)) (getr regs 9).
stepLD8 (ltac:(oF' 0x988dc%Z)) (ltac:(oD' 0x988dc%Z)) (getr regs 18).
stepLD8 (ltac:(oF' 0x988e0%Z)) (ltac:(oD' 0x988e0%Z)) (getr regs 19).
stepn (ltac:(oF' 0x988e4%Z)) (ltac:(oD' 0x988e4%Z)). sp_renorm.
stepn (ltac:(oF' 0x988e8%Z)) (ltac:(oD' 0x988e8%Z)).
stepLD (ltac:(oF' 0xaa078%Z)) (ltac:(oD' 0xaa078%Z)) (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_by Mxl) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
stepb_ft (ltac:(oF' 0xaa07c%Z)) (ltac:(oD' 0xaa07c%Z)) ltac:(cond_compute).
stepret (ltac:(oF' 0xaa080%Z)) (ltac:(oD' 0xaa080%Z)) (0x98b34 : word) ltac:(bveq).
stepn (ltac:(oF' 0x98b34%Z)) (ltac:(oD' 0x98b34%Z)).
apply mst_refl.
- repeat split; gres; try reflexivity. exact Htp. }
{
destruct AX as (Mcb & Mxl & Msl & Mxh & Mnx & Mf0 & Ma0). unfold mem_w1, ax_writes. eexists. split.
-
stepn (ltac:(oF' 0x98ad0%Z)) (ltac:(oD' 0x98ad0%Z)). rewrite Hsp. sp_renorm.
stepST (ltac:(oF' 0x98ad4%Z)) (ltac:(oD' 0x98ad4%Z)) (Z_to_bv 64 (bv_unsigned sp - 8)) (getr regs 1) ltac:(sok_stack SOK).
stepST (ltac:(oF' 0x98ad8%Z)) (ltac:(oD' 0x98ad8%Z)) (Z_to_bv 64 (bv_unsigned sp - 16)) (getr regs 8) ltac:(sok_stack SOK).
stepn (ltac:(oF' 0x98adc%Z)) (ltac:(oD' 0x98adc%Z)).
stepn (ltac:(oF' 0x98ae0%Z)) (ltac:(oD' 0x98ae0%Z)). rewrite Htp.
stepLD (ltac:(oF' 0x98ae4%Z)) (ltac:(oD' 0x98ae4%Z)) (word_to_le_bytes 4 (Z_to_bv 64 tid)) (Z_to_bv 64 tid)
ltac:(change (v_addi tp (-168)) with (Z_to_bv 64 (bv_unsigned tp - 168)); rdn_by Mtid)
ltac:(apply bytes_le_to_Z_4; u_norm; lia).
rewrite (v_lw_small tid) by lia.
stepn (ltac:(oF' 0x98ae8%Z)) (ltac:(oD' 0x98ae8%Z)).
stepn (ltac:(oF' 0x98aec%Z)) (ltac:(oD' 0x98aec%Z)).
eapply mst_step; [reflexivity
| eapply step_lr_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
[ exact (ltac:(oF' 0x98af0%Z)) | reflexivity | exact (ltac:(oD' 0x98af0%Z))
| gres; u_norm; reflexivity
| gres; rdn_by Mlock
| apply bytes_le_to_Z_4; u_norm; lia ]
| ].
reduce_bv_eqb_ifs; norm_pc_r; vnorm.
eapply mst_step; [reflexivity
| eapply step_bne_ft_r; [exact (ltac:(oF' 0x98af4%Z)) | reflexivity | exact (ltac:(oD' 0x98af4%Z)) | gres; cond_compute ] | ].
norm_pc_r.
eapply mst_step; [reflexivity
| eapply step_sc_w_ok; [exact (ltac:(oF' 0x98af8%Z)) | reflexivity | exact (ltac:(oD' 0x98af8%Z))
| gres; u_norm; reflexivity | gres; reflexivity | gres; sok_data ] | ].
step_simpl; vnorm.
stepb_ft (ltac:(oF' 0x98afc%Z)) (ltac:(oD' 0x98afc%Z)) ltac:(cond_compute).
stepn (ltac:(oF' 0x98b00%Z)) (ltac:(oD' 0x98b00%Z)).
stepb_ft (ltac:(oF' 0x98b04%Z)) (ltac:(oD' 0x98b04%Z)) ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; u_norm; lia).
stepb_tk (ltac:(oF' 0x98b08%Z)) (ltac:(oD' 0x98b08%Z)) ltac:(cond_compute).
stepn (ltac:(oF' 0x98b2c%Z)) (ltac:(oD' 0x98b2c%Z)). rewrite Ha0.
stepn (ltac:(oF' 0x98b30%Z)) (ltac:(oD' 0x98b30%Z)).
stepn (ltac:(oF' 0x98824%Z)) (ltac:(oD' 0x98824%Z)). sp_renorm.
stepST (ltac:(oF' 0x98828%Z)) (ltac:(oD' 0x98828%Z)) (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x98b34) ltac:(sok_stack SOK).
stepST (ltac:(oF' 0x9882c%Z)) (ltac:(oD' 0x9882c%Z)) (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
stepST (ltac:(oF' 0x98830%Z)) (ltac:(oD' 0x98830%Z)) (Z_to_bv 64 (bv_unsigned sp - 40)) (getr regs 9) ltac:(sok_stack SOK).
stepST (ltac:(oF' 0x98834%Z)) (ltac:(oD' 0x98834%Z)) (Z_to_bv 64 (bv_unsigned sp - 48)) (getr regs 18) ltac:(sok_stack SOK).
stepST (ltac:(oF' 0x98838%Z)) (ltac:(oD' 0x98838%Z)) (Z_to_bv 64 (bv_unsigned sp - 56)) (getr regs 19) ltac:(sok_stack SOK).
stepn (ltac:(oF' 0x9883c%Z)) (ltac:(oD' 0x9883c%Z)). stepn (ltac:(oF' 0x98840%Z)) (ltac:(oD' 0x98840%Z)). stepn (ltac:(oF' 0x98844%Z)) (ltac:(oD' 0x98844%Z)). stepn (ltac:(oF' 0x98848%Z)) (ltac:(oD' 0x98848%Z)).
stepn (ltac:(oF' 0x9884c%Z)) (ltac:(oD' 0x9884c%Z)).
stepn (ltac:(oF' 0xa9df0%Z)) (ltac:(oD' 0xa9df0%Z)).
chain_step; [reflexivity
| eapply step_lb with (b := Z_to_bv 8 0);
[exact (ltac:(oF' 0xa9df4%Z)) | reflexivity | exact (ltac:(oD' 0xa9df4%Z)) | gres; imm_norm; addr_norm; rdn_by Gnl]
| step_simpl]; vnorm.
stepb_tk (ltac:(oF' 0xa9df8%Z)) (ltac:(oD' 0xa9df8%Z)) ltac:(cond_compute).
stepret (ltac:(oF' 0xa9fe8%Z)) (ltac:(oD' 0xa9fe8%Z)) (0x98850 : word) ltac:(bveq).
stepLD (ltac:(oF' 0x98850%Z)) (ltac:(oD' 0x98850%Z)) (word_to_le_bytes 8 (Z_to_bv 64 0xe7cc0)) (Z_to_bv 64 0xe7cc0) ltac:(addr_norm; rdn_by Mxh) ltac:(apply bytes_le_to_Z_8).
stepb_ft (ltac:(oF' 0x98854%Z)) (ltac:(oD' 0x98854%Z)) ltac:(cond_compute).
stepLD (ltac:(oF' 0x98858%Z)) (ltac:(oD' 0x98858%Z)) (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(addr_norm; rdn_by Msl) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
stepn (ltac:(oF' 0x9885c%Z)) (ltac:(oD' 0x9885c%Z)).
stepn (ltac:(oF' 0x98874%Z)) (ltac:(oD' 0x98874%Z)).
stepST (ltac:(oF' 0x98878%Z)) (ltac:(oD' 0x98878%Z)) (Z_to_bv 64 0xe7cb0) (Z_to_bv 64 0) ltac:(sok_data).
stepb_ft (ltac:(oF' 0x9887c%Z)) (ltac:(oD' 0x9887c%Z)) ltac:(cond_compute).
stepLD (ltac:(oF' 0x98880%Z)) (ltac:(oD' 0x98880%Z)) (word_to_le_bytes 8 (Z_to_bv 64 0xe7cc0)) (Z_to_bv 64 0xe7cc0) ltac:(addr_norm; rdn_by Mxh) ltac:(apply bytes_le_to_Z_8).
stepn (ltac:(oF' 0x98884%Z)) (ltac:(oD' 0x98884%Z)).
stepn (ltac:(oF' 0x98888%Z)) (ltac:(oD' 0x98888%Z)).
stepLD (ltac:(oF' 0x9888c%Z)) (ltac:(oD' 0x9888c%Z)) (word_to_le_bytes 8 (Z_to_bv 64 0x98a7c)) (Z_to_bv 64 0x98a7c) ltac:(addr_norm; rdn_by Mf0) ltac:(apply bytes_le_to_Z_8).
stepLD (ltac:(oF' 0x98890%Z)) (ltac:(oD' 0x98890%Z)) (word_to_le_bytes 8 (Z_to_bv 64 0x33fd4)) (Z_to_bv 64 0x33fd4) ltac:(addr_norm; rdn_by Ma0) ltac:(apply bytes_le_to_Z_8).
stepn (ltac:(oF' 0x98894%Z)) (ltac:(oD' 0x98894%Z)).
stepn (ltac:(oF' 0x98898%Z)) (ltac:(oD' 0x98898%Z)).
stepLD (ltac:(oF' 0xaa078%Z)) (ltac:(oD' 0xaa078%Z)) (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_by Mxl) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
stepb_ft (ltac:(oF' 0xaa07c%Z)) (ltac:(oD' 0xaa07c%Z)) ltac:(cond_compute).
stepret (ltac:(oF' 0xaa080%Z)) (ltac:(oD' 0xaa080%Z)) (0x9889c : word) ltac:(bveq).
stepn (ltac:(oF' 0x9889c%Z)) (ltac:(oD' 0x9889c%Z)).
stepret (ltac:(oF' 0x988a0%Z)) (ltac:(oD' 0x988a0%Z)) (0x98a7c : word) ltac:(bveq).
stepret (ltac:(oF' 0x98a7c%Z)) (ltac:(oD' 0x98a7c%Z)) (0x33fd4 : word) ltac:(bveq).
stepn (ltac:(oF' 0x33fd4%Z)) (ltac:(oD' 0x33fd4%Z)).
stepLBU (ltac:(oF' 0x33fd8%Z)) (ltac:(oD' 0x33fd8%Z)) (Z_to_bv 8 0) ltac:(addr_norm; rdn_by Mcb).
stepb_ft (ltac:(oF' 0x33fdc%Z)) (ltac:(oD' 0x33fdc%Z)) ltac:(cond_compute).
stepret (ltac:(oF' 0x33fe0%Z)) (ltac:(oD' 0x33fe0%Z)) (0x988a4 : word) ltac:(bveq).
stepn (ltac:(oF' 0x988a4%Z)) (ltac:(oD' 0x988a4%Z)).
stepn (ltac:(oF' 0x988a8%Z)) (ltac:(oD' 0x988a8%Z)).
stepn (ltac:(oF' 0xa9df0%Z)) (ltac:(oD' 0xa9df0%Z)).
chain_step; [reflexivity
| eapply step_lb with (b := Z_to_bv 8 0);
[exact (ltac:(oF' 0xa9df4%Z)) | reflexivity | exact (ltac:(oD' 0xa9df4%Z)) | gres; imm_norm; addr_norm; rdn_by Gnl]
| step_simpl]; vnorm.
stepb_tk (ltac:(oF' 0xa9df8%Z)) (ltac:(oD' 0xa9df8%Z)) ltac:(cond_compute).
stepret (ltac:(oF' 0xa9fe8%Z)) (ltac:(oD' 0xa9fe8%Z)) (0x988ac : word) ltac:(bveq).
stepLD (ltac:(oF' 0x988ac%Z)) (ltac:(oD' 0x988ac%Z)) (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0)
ltac:(addr_norm; lazymatch goal with |- rdn ?s (wbytes ?m ?a ?bs) _ _ = _ => pose proof (rdn_wbytes_hit s bs m a) as HH; rewrite length_N_to_le_bytes in HH; apply HH; zsimp; lia end)
ltac:(apply bytes_le_to_Z_4; u_norm; lia).
stepn (ltac:(oF' 0x988b0%Z)) (ltac:(oD' 0x988b0%Z)).
stepST (ltac:(oF' 0x988b4%Z)) (ltac:(oD' 0x988b4%Z)) (Z_to_bv 64 0xe7cb0) (Z_to_bv 64 18446744073709551615) ltac:(sok_data).
stepb_ft (ltac:(oF' 0x988b8%Z)) (ltac:(oD' 0x988b8%Z)) ltac:(cond_compute).
stepLD (ltac:(oF' 0x988bc%Z)) (ltac:(oD' 0x988bc%Z)) (word_to_le_bytes 8 (Z_to_bv 64 0xe7cc0)) (Z_to_bv 64 0xe7cc0) ltac:(addr_norm; rdn_by Mxh) ltac:(apply bytes_le_to_Z_8).
stepn (ltac:(oF' 0x988c0%Z)) (ltac:(oD' 0x988c0%Z)).
stepLD (ltac:(oF' 0x98860%Z)) (ltac:(oD' 0x98860%Z)) (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_by Mnx) ltac:(apply bytes_le_to_Z_8).
stepn (ltac:(oF' 0x98864%Z)) (ltac:(oD' 0x98864%Z)).
stepST (ltac:(oF' 0x98868%Z)) (ltac:(oD' 0x98868%Z)) (Z_to_bv 64 0xe7cb0) (Z_to_bv 64 32) ltac:(sok_data).
stepST (ltac:(oF' 0x9886c%Z)) (ltac:(oD' 0x9886c%Z)) (Z_to_bv 64 0xe7cb8) (Z_to_bv 64 0) ltac:(sok_data).
stepb_tk (ltac:(oF' 0x98870%Z)) (ltac:(oD' 0x98870%Z)) ltac:(cond_compute).
stepn (ltac:(oF' 0x988c4%Z)) (ltac:(oD' 0x988c4%Z)).
stepST (ltac:(oF' 0x988c8%Z)) (ltac:(oD' 0x988c8%Z)) (Z_to_bv 64 0xe7ca8) (Z_to_bv 64 1) ltac:(sok_data).
change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
stepn (ltac:(oF' 0x988cc%Z)) (ltac:(oD' 0x988cc%Z)).
stepLD8 (ltac:(oF' 0x988d0%Z)) (ltac:(oD' 0x988d0%Z)) (Z_to_bv 64 0x98b34).
stepLD8 (ltac:(oF' 0x988d4%Z)) (ltac:(oD' 0x988d4%Z)) code.
stepLD8 (ltac:(oF' 0x988d8%Z)) (ltac:(oD' 0x988d8%Z)) (getr regs 9).
stepLD8 (ltac:(oF' 0x988dc%Z)) (ltac:(oD' 0x988dc%Z)) (getr regs 18).
stepLD8 (ltac:(oF' 0x988e0%Z)) (ltac:(oD' 0x988e0%Z)) (getr regs 19).
stepn (ltac:(oF' 0x988e4%Z)) (ltac:(oD' 0x988e4%Z)). sp_renorm.
stepn (ltac:(oF' 0x988e8%Z)) (ltac:(oD' 0x988e8%Z)).
stepLD (ltac:(oF' 0xaa078%Z)) (ltac:(oD' 0xaa078%Z)) (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_by Mxl) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
stepb_ft (ltac:(oF' 0xaa07c%Z)) (ltac:(oD' 0xaa07c%Z)) ltac:(cond_compute).
stepret (ltac:(oF' 0xaa080%Z)) (ltac:(oD' 0xaa080%Z)) (0x98b34 : word) ltac:(bveq).
stepn (ltac:(oF' 0x98b34%Z)) (ltac:(oD' 0x98b34%Z)).
apply mst_refl.
- repeat split; gres; try reflexivity. exact Htp. }
{
destruct AX as (Mcb & Mxl & Msl & Mxh & Mnx & Mf0 & Ma0 & Mf1 & Ma1). unfold mem_w1, ax_writes. eexists. split.
-
stepn (ltac:(oF' 0x98ad0%Z)) (ltac:(oD' 0x98ad0%Z)). rewrite Hsp. sp_renorm.
stepST (ltac:(oF' 0x98ad4%Z)) (ltac:(oD' 0x98ad4%Z)) (Z_to_bv 64 (bv_unsigned sp - 8)) (getr regs 1) ltac:(sok_stack SOK).
stepST (ltac:(oF' 0x98ad8%Z)) (ltac:(oD' 0x98ad8%Z)) (Z_to_bv 64 (bv_unsigned sp - 16)) (getr regs 8) ltac:(sok_stack SOK).
stepn (ltac:(oF' 0x98adc%Z)) (ltac:(oD' 0x98adc%Z)).
stepn (ltac:(oF' 0x98ae0%Z)) (ltac:(oD' 0x98ae0%Z)). rewrite Htp.
stepLD (ltac:(oF' 0x98ae4%Z)) (ltac:(oD' 0x98ae4%Z)) (word_to_le_bytes 4 (Z_to_bv 64 tid)) (Z_to_bv 64 tid)
ltac:(change (v_addi tp (-168)) with (Z_to_bv 64 (bv_unsigned tp - 168)); rdn_by Mtid)
ltac:(apply bytes_le_to_Z_4; u_norm; lia).
rewrite (v_lw_small tid) by lia.
stepn (ltac:(oF' 0x98ae8%Z)) (ltac:(oD' 0x98ae8%Z)).
stepn (ltac:(oF' 0x98aec%Z)) (ltac:(oD' 0x98aec%Z)).
eapply mst_step; [reflexivity
| eapply step_lr_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
[ exact (ltac:(oF' 0x98af0%Z)) | reflexivity | exact (ltac:(oD' 0x98af0%Z))
| gres; u_norm; reflexivity
| gres; rdn_by Mlock
| apply bytes_le_to_Z_4; u_norm; lia ]
| ].
reduce_bv_eqb_ifs; norm_pc_r; vnorm.
eapply mst_step; [reflexivity
| eapply step_bne_ft_r; [exact (ltac:(oF' 0x98af4%Z)) | reflexivity | exact (ltac:(oD' 0x98af4%Z)) | gres; cond_compute ] | ].
norm_pc_r.
eapply mst_step; [reflexivity
| eapply step_sc_w_ok; [exact (ltac:(oF' 0x98af8%Z)) | reflexivity | exact (ltac:(oD' 0x98af8%Z))
| gres; u_norm; reflexivity | gres; reflexivity | gres; sok_data ] | ].
step_simpl; vnorm.
stepb_ft (ltac:(oF' 0x98afc%Z)) (ltac:(oD' 0x98afc%Z)) ltac:(cond_compute).
stepn (ltac:(oF' 0x98b00%Z)) (ltac:(oD' 0x98b00%Z)).
stepb_ft (ltac:(oF' 0x98b04%Z)) (ltac:(oD' 0x98b04%Z)) ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; u_norm; lia).
stepb_tk (ltac:(oF' 0x98b08%Z)) (ltac:(oD' 0x98b08%Z)) ltac:(cond_compute).
stepn (ltac:(oF' 0x98b2c%Z)) (ltac:(oD' 0x98b2c%Z)). rewrite Ha0.
stepn (ltac:(oF' 0x98b30%Z)) (ltac:(oD' 0x98b30%Z)).
stepn (ltac:(oF' 0x98824%Z)) (ltac:(oD' 0x98824%Z)). sp_renorm.
stepST (ltac:(oF' 0x98828%Z)) (ltac:(oD' 0x98828%Z)) (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x98b34) ltac:(sok_stack SOK).
stepST (ltac:(oF' 0x9882c%Z)) (ltac:(oD' 0x9882c%Z)) (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
stepST (ltac:(oF' 0x98830%Z)) (ltac:(oD' 0x98830%Z)) (Z_to_bv 64 (bv_unsigned sp - 40)) (getr regs 9) ltac:(sok_stack SOK).
stepST (ltac:(oF' 0x98834%Z)) (ltac:(oD' 0x98834%Z)) (Z_to_bv 64 (bv_unsigned sp - 48)) (getr regs 18) ltac:(sok_stack SOK).
stepST (ltac:(oF' 0x98838%Z)) (ltac:(oD' 0x98838%Z)) (Z_to_bv 64 (bv_unsigned sp - 56)) (getr regs 19) ltac:(sok_stack SOK).
stepn (ltac:(oF' 0x9883c%Z)) (ltac:(oD' 0x9883c%Z)). stepn (ltac:(oF' 0x98840%Z)) (ltac:(oD' 0x98840%Z)). stepn (ltac:(oF' 0x98844%Z)) (ltac:(oD' 0x98844%Z)). stepn (ltac:(oF' 0x98848%Z)) (ltac:(oD' 0x98848%Z)).
stepn (ltac:(oF' 0x9884c%Z)) (ltac:(oD' 0x9884c%Z)).
stepn (ltac:(oF' 0xa9df0%Z)) (ltac:(oD' 0xa9df0%Z)).
chain_step; [reflexivity
| eapply step_lb with (b := Z_to_bv 8 0);
[exact (ltac:(oF' 0xa9df4%Z)) | reflexivity | exact (ltac:(oD' 0xa9df4%Z)) | gres; imm_norm; addr_norm; rdn_by Gnl]
| step_simpl]; vnorm.
stepb_tk (ltac:(oF' 0xa9df8%Z)) (ltac:(oD' 0xa9df8%Z)) ltac:(cond_compute).
stepret (ltac:(oF' 0xa9fe8%Z)) (ltac:(oD' 0xa9fe8%Z)) (0x98850 : word) ltac:(bveq).
stepLD (ltac:(oF' 0x98850%Z)) (ltac:(oD' 0x98850%Z)) (word_to_le_bytes 8 (Z_to_bv 64 0xe7cc0)) (Z_to_bv 64 0xe7cc0) ltac:(addr_norm; rdn_by Mxh) ltac:(apply bytes_le_to_Z_8).
stepb_ft (ltac:(oF' 0x98854%Z)) (ltac:(oD' 0x98854%Z)) ltac:(cond_compute).
stepLD (ltac:(oF' 0x98858%Z)) (ltac:(oD' 0x98858%Z)) (word_to_le_bytes 4 (Z_to_bv 64 2)) (Z_to_bv 64 2) ltac:(addr_norm; rdn_by Msl) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
stepn (ltac:(oF' 0x9885c%Z)) (ltac:(oD' 0x9885c%Z)).
stepn (ltac:(oF' 0x98874%Z)) (ltac:(oD' 0x98874%Z)).
stepST (ltac:(oF' 0x98878%Z)) (ltac:(oD' 0x98878%Z)) (Z_to_bv 64 0xe7cb0) (Z_to_bv 64 1) ltac:(sok_data).
stepb_ft (ltac:(oF' 0x9887c%Z)) (ltac:(oD' 0x9887c%Z)) ltac:(cond_compute).
stepLD (ltac:(oF' 0x98880%Z)) (ltac:(oD' 0x98880%Z)) (word_to_le_bytes 8 (Z_to_bv 64 0xe7cc0)) (Z_to_bv 64 0xe7cc0) ltac:(addr_norm; rdn_by Mxh) ltac:(apply bytes_le_to_Z_8).
stepn (ltac:(oF' 0x98884%Z)) (ltac:(oD' 0x98884%Z)).
stepn (ltac:(oF' 0x98888%Z)) (ltac:(oD' 0x98888%Z)).
stepLD (ltac:(oF' 0x9888c%Z)) (ltac:(oD' 0x9888c%Z)) (word_to_le_bytes 8 (Z_to_bv 64 0x55b78)) (Z_to_bv 64 0x55b78) ltac:(addr_norm; rdn_by Mf1) ltac:(apply bytes_le_to_Z_8).
stepLD (ltac:(oF' 0x98890%Z)) (ltac:(oD' 0x98890%Z)) (word_to_le_bytes 8 (Z_to_bv 64 0xb5f20)) (Z_to_bv 64 0xb5f20) ltac:(addr_norm; rdn_by Ma1) ltac:(apply bytes_le_to_Z_8).
stepn (ltac:(oF' 0x98894%Z)) (ltac:(oD' 0x98894%Z)).
stepn (ltac:(oF' 0x98898%Z)) (ltac:(oD' 0x98898%Z)).
stepLD (ltac:(oF' 0xaa078%Z)) (ltac:(oD' 0xaa078%Z)) (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_by Mxl) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
stepb_ft (ltac:(oF' 0xaa07c%Z)) (ltac:(oD' 0xaa07c%Z)) ltac:(cond_compute).
stepret (ltac:(oF' 0xaa080%Z)) (ltac:(oD' 0xaa080%Z)) (0x9889c : word) ltac:(bveq).
stepn (ltac:(oF' 0x9889c%Z)) (ltac:(oD' 0x9889c%Z)).
stepret (ltac:(oF' 0x988a0%Z)) (ltac:(oD' 0x988a0%Z)) (0x55b78 : word) ltac:(bveq).
stepret (ltac:(oF' 0x55b78%Z)) (ltac:(oD' 0x55b78%Z)) (0x988a4 : word) ltac:(bveq).
stepn (ltac:(oF' 0x988a4%Z)) (ltac:(oD' 0x988a4%Z)).
stepn (ltac:(oF' 0x988a8%Z)) (ltac:(oD' 0x988a8%Z)).
stepn (ltac:(oF' 0xa9df0%Z)) (ltac:(oD' 0xa9df0%Z)).
chain_step; [reflexivity
| eapply step_lb with (b := Z_to_bv 8 0);
[exact (ltac:(oF' 0xa9df4%Z)) | reflexivity | exact (ltac:(oD' 0xa9df4%Z)) | gres; imm_norm; addr_norm; rdn_by Gnl]
| step_simpl]; vnorm.
stepb_tk (ltac:(oF' 0xa9df8%Z)) (ltac:(oD' 0xa9df8%Z)) ltac:(cond_compute).
stepret (ltac:(oF' 0xa9fe8%Z)) (ltac:(oD' 0xa9fe8%Z)) (0x988ac : word) ltac:(bveq).
stepLD (ltac:(oF' 0x988ac%Z)) (ltac:(oD' 0x988ac%Z)) (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1)
ltac:(addr_norm; lazymatch goal with |- rdn ?s (wbytes ?m ?a ?bs) _ _ = _ => pose proof (rdn_wbytes_hit s bs m a) as HH; rewrite length_N_to_le_bytes in HH; apply HH; zsimp; lia end)
ltac:(apply bytes_le_to_Z_4; u_norm; lia).
stepn (ltac:(oF' 0x988b0%Z)) (ltac:(oD' 0x988b0%Z)).
stepST (ltac:(oF' 0x988b4%Z)) (ltac:(oD' 0x988b4%Z)) (Z_to_bv 64 0xe7cb0) (Z_to_bv 64 0) ltac:(sok_data).
stepb_tk (ltac:(oF' 0x988b8%Z)) (ltac:(oD' 0x988b8%Z)) ltac:(cond_compute).
stepLD (ltac:(oF' 0x98880%Z)) (ltac:(oD' 0x98880%Z)) (word_to_le_bytes 8 (Z_to_bv 64 0xe7cc0)) (Z_to_bv 64 0xe7cc0) ltac:(addr_norm; rdn_by Mxh) ltac:(apply bytes_le_to_Z_8).
stepn (ltac:(oF' 0x98884%Z)) (ltac:(oD' 0x98884%Z)).
stepn (ltac:(oF' 0x98888%Z)) (ltac:(oD' 0x98888%Z)).
stepLD (ltac:(oF' 0x9888c%Z)) (ltac:(oD' 0x9888c%Z)) (word_to_le_bytes 8 (Z_to_bv 64 0x98a7c)) (Z_to_bv 64 0x98a7c) ltac:(addr_norm; rdn_by Mf0) ltac:(apply bytes_le_to_Z_8).
stepLD (ltac:(oF' 0x98890%Z)) (ltac:(oD' 0x98890%Z)) (word_to_le_bytes 8 (Z_to_bv 64 0x33fd4)) (Z_to_bv 64 0x33fd4) ltac:(addr_norm; rdn_by Ma0) ltac:(apply bytes_le_to_Z_8).
stepn (ltac:(oF' 0x98894%Z)) (ltac:(oD' 0x98894%Z)).
stepn (ltac:(oF' 0x98898%Z)) (ltac:(oD' 0x98898%Z)).
stepLD (ltac:(oF' 0xaa078%Z)) (ltac:(oD' 0xaa078%Z)) (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_by Mxl) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
stepb_ft (ltac:(oF' 0xaa07c%Z)) (ltac:(oD' 0xaa07c%Z)) ltac:(cond_compute).
stepret (ltac:(oF' 0xaa080%Z)) (ltac:(oD' 0xaa080%Z)) (0x9889c : word) ltac:(bveq).
stepn (ltac:(oF' 0x9889c%Z)) (ltac:(oD' 0x9889c%Z)).
stepret (ltac:(oF' 0x988a0%Z)) (ltac:(oD' 0x988a0%Z)) (0x98a7c : word) ltac:(bveq).
stepret (ltac:(oF' 0x98a7c%Z)) (ltac:(oD' 0x98a7c%Z)) (0x33fd4 : word) ltac:(bveq).
stepn (ltac:(oF' 0x33fd4%Z)) (ltac:(oD' 0x33fd4%Z)).
stepLBU (ltac:(oF' 0x33fd8%Z)) (ltac:(oD' 0x33fd8%Z)) (Z_to_bv 8 0) ltac:(addr_norm; rdn_by Mcb).
stepb_ft (ltac:(oF' 0x33fdc%Z)) (ltac:(oD' 0x33fdc%Z)) ltac:(cond_compute).
stepret (ltac:(oF' 0x33fe0%Z)) (ltac:(oD' 0x33fe0%Z)) (0x988a4 : word) ltac:(bveq).
stepn (ltac:(oF' 0x988a4%Z)) (ltac:(oD' 0x988a4%Z)).
stepn (ltac:(oF' 0x988a8%Z)) (ltac:(oD' 0x988a8%Z)).
stepn (ltac:(oF' 0xa9df0%Z)) (ltac:(oD' 0xa9df0%Z)).
chain_step; [reflexivity
| eapply step_lb with (b := Z_to_bv 8 0);
[exact (ltac:(oF' 0xa9df4%Z)) | reflexivity | exact (ltac:(oD' 0xa9df4%Z)) | gres; imm_norm; addr_norm; rdn_by Gnl]
| step_simpl]; vnorm.
stepb_tk (ltac:(oF' 0xa9df8%Z)) (ltac:(oD' 0xa9df8%Z)) ltac:(cond_compute).
stepret (ltac:(oF' 0xa9fe8%Z)) (ltac:(oD' 0xa9fe8%Z)) (0x988ac : word) ltac:(bveq).
stepLD (ltac:(oF' 0x988ac%Z)) (ltac:(oD' 0x988ac%Z)) (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0)
ltac:(addr_norm; lazymatch goal with |- rdn ?s (wbytes ?m ?a ?bs) _ _ = _ => pose proof (rdn_wbytes_hit s bs m a) as HH; rewrite length_N_to_le_bytes in HH; apply HH; zsimp; lia end)
ltac:(apply bytes_le_to_Z_4; u_norm; lia).
stepn (ltac:(oF' 0x988b0%Z)) (ltac:(oD' 0x988b0%Z)).
stepST (ltac:(oF' 0x988b4%Z)) (ltac:(oD' 0x988b4%Z)) (Z_to_bv 64 0xe7cb0) (Z_to_bv 64 18446744073709551615) ltac:(sok_data).
stepb_ft (ltac:(oF' 0x988b8%Z)) (ltac:(oD' 0x988b8%Z)) ltac:(cond_compute).
stepLD (ltac:(oF' 0x988bc%Z)) (ltac:(oD' 0x988bc%Z)) (word_to_le_bytes 8 (Z_to_bv 64 0xe7cc0)) (Z_to_bv 64 0xe7cc0) ltac:(addr_norm; rdn_by Mxh) ltac:(apply bytes_le_to_Z_8).
stepn (ltac:(oF' 0x988c0%Z)) (ltac:(oD' 0x988c0%Z)).
stepLD (ltac:(oF' 0x98860%Z)) (ltac:(oD' 0x98860%Z)) (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_by Mnx) ltac:(apply bytes_le_to_Z_8).
stepn (ltac:(oF' 0x98864%Z)) (ltac:(oD' 0x98864%Z)).
stepST (ltac:(oF' 0x98868%Z)) (ltac:(oD' 0x98868%Z)) (Z_to_bv 64 0xe7cb0) (Z_to_bv 64 32) ltac:(sok_data).
stepST (ltac:(oF' 0x9886c%Z)) (ltac:(oD' 0x9886c%Z)) (Z_to_bv 64 0xe7cb8) (Z_to_bv 64 0) ltac:(sok_data).
stepb_tk (ltac:(oF' 0x98870%Z)) (ltac:(oD' 0x98870%Z)) ltac:(cond_compute).
stepn (ltac:(oF' 0x988c4%Z)) (ltac:(oD' 0x988c4%Z)).
stepST (ltac:(oF' 0x988c8%Z)) (ltac:(oD' 0x988c8%Z)) (Z_to_bv 64 0xe7ca8) (Z_to_bv 64 1) ltac:(sok_data).
change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
stepn (ltac:(oF' 0x988cc%Z)) (ltac:(oD' 0x988cc%Z)).
stepLD8 (ltac:(oF' 0x988d0%Z)) (ltac:(oD' 0x988d0%Z)) (Z_to_bv 64 0x98b34).
stepLD8 (ltac:(oF' 0x988d4%Z)) (ltac:(oD' 0x988d4%Z)) code.
stepLD8 (ltac:(oF' 0x988d8%Z)) (ltac:(oD' 0x988d8%Z)) (getr regs 9).
stepLD8 (ltac:(oF' 0x988dc%Z)) (ltac:(oD' 0x988dc%Z)) (getr regs 18).
stepLD8 (ltac:(oF' 0x988e0%Z)) (ltac:(oD' 0x988e0%Z)) (getr regs 19).
stepn (ltac:(oF' 0x988e4%Z)) (ltac:(oD' 0x988e4%Z)). sp_renorm.
stepn (ltac:(oF' 0x988e8%Z)) (ltac:(oD' 0x988e8%Z)).
stepLD (ltac:(oF' 0xaa078%Z)) (ltac:(oD' 0xaa078%Z)) (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_by Mxl) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
stepb_ft (ltac:(oF' 0xaa07c%Z)) (ltac:(oD' 0xaa07c%Z)) ltac:(cond_compute).
stepret (ltac:(oF' 0xaa080%Z)) (ltac:(oD' 0xaa080%Z)) (0x98b34 : word) ltac:(bveq).
stepn (ltac:(oF' 0x98b34%Z)) (ltac:(oD' 0x98b34%Z)).
apply mst_refl.
- repeat split; gres; try reflexivity. exact Htp. }
Qed.
Definition mem_w2 (mem : word -> option byte) (sp code s1v : word) :=
wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
(Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x98b38)))
(Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
(Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 s1v))
(Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 (Z_to_bv 64 0x98ab4)))
(Z_to_bv 64 (bv_unsigned sp - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0xaf1d0)))
(Z_to_bv 64 0xb6228) [Z_to_bv 8 1].
Section SE.
Local Abbreviation SEC_T_w2 := (ltac2:(TCodec.tc2 tcn__Js0Exit_run1 "V>&=y5'Q0yR0%211%5241'5y8%611%311p061'9&@r6(N+2(7%33@21%6251&O&E&Q1r3%22D1+@%5221%72G1%@3G91r7+8%@3M1>%C231%E3L1:r8+1%E3Q21C%H231+cRiH%C2Q31%L3Q331r9+9%L3Q91J%O231r4%Q23Q921&D+TPPPPP0%K2Q=D+T@%N221%5241%O2QAC+TPPPPPPPP0%8221'1&;&Cr;%Q62QHC%Q821;%Q:2QJ1uT@%746521(6%QF3:21'3%11QK%QN11&Br<+fcf@%QE2R51u8%54A421(0&<+el^H%QK2R;1%3261%52=1%R63=71r=+fcfH%R12RA1%@4L31<+el^@%R42RD1%<2?1%>2F1%R?3F51r>%G4Q315C+V^hL%R;2RK1%C2F1%E2M1%RF3M51r?+fha8%RA2S11u1%Q14Q=421(2z%RF2S21(4%11S3%53S431%Q22Q:1%S33Q:81r@+fc[0%RN2S>1%Q=4QI31Q9+cRW<%S12SA1%Q92Q<1%Q;2QC1%S<3QC51rA+fggH%S72SG1%QF4R231QB%Q@2QC2%QB2QJ1%SC3QJ31rB+fc[8%S>2SN1%QM4R931QI%S@2T0K%QH2QK1%QJ2R21%SK3R241':'8'>&AvGrE+cRd4%T03T;1SN/01T;rDrC%8576321r1+chVH%T73TB1T5/01TB&?%148IQ0Q9%?5>6318%A3S181%T?28T:%T72TIM%T921T5%T;2TK1%TD3TK41%TD2=T2%TF3TM1Q9%TF2?SO+cRiL%TA2U11%TJ3U131%TJ2CSL%TL3U31QH+4%TK3U81TI%TN2G1%TO2O2%U13U821+3%U03U=1TN%U32L1%U42Q42%U63U=21%Q:261%Q;2<1%Q<2?1%Q=2D1%Q>2G1%Q?2M1qQFUC1%QB2UD1p0QD1p0QM1p0R51p0R?1p0RM1p0S51p0S?1p0T01p0T<1p0T@1p0TG1p0TN1p0U61p0U<1pQJV41pQ>V51pQLV61pQHV11pQBV21pQDV81")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_w2) 0%nat 0%nat).
Variable mem : ltac:(sec_ty2 constr:(SEC_T_w2) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_w2) 2%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_w2) 3%nat 0%nat).
Variable code : ltac:(sec_ty2 constr:(SEC_T_w2) 4%nat 0%nat).
Variable s1v : ltac:(sec_ty2 constr:(SEC_T_w2) 5%nat 0%nat).
Lemma w2 : ltac:(sec_stmt2 constr:(SEC_T_w2) 6%nat 0%nat).
Proof.
intros Hsp Hs0 Hra Hs1 SPlo SPhi SOK Mfe Mfs Mfa Mcomp Mg1 Mdso Mg2.
unfold mem_w2. eexists. split.
-
stepn (ltac:(oF' 0x98a84%Z)) (ltac:(oD' 0x98a84%Z)). rewrite Hsp. sp_renorm.
stepST (ltac:(oF' 0x98a88%Z)) (ltac:(oD' 0x98a88%Z)) (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x98b38) ltac:(sok_stack SOK).
stepST (ltac:(oF' 0x98a8c%Z)) (ltac:(oD' 0x98a8c%Z)) (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
stepST (ltac:(oF' 0x98a90%Z)) (ltac:(oD' 0x98a90%Z)) (Z_to_bv 64 (bv_unsigned sp - 40)) s1v ltac:(sok_stack SOK).
stepn (ltac:(oF' 0x98a94%Z)) (ltac:(oD' 0x98a94%Z)).
stepn (ltac:(oF' 0x98a98%Z)) (ltac:(oD' 0x98a98%Z)).
stepLD8 (ltac:(oF' 0x98a9c%Z)) (ltac:(oD' 0x98a9c%Z)) (Z_to_bv 64 0xaf1d8).
stepLD8 (ltac:(oF' 0x98aa0%Z)) (ltac:(oD' 0x98aa0%Z)) (Z_to_bv 64 0xaf1d0).
stepb_ft (ltac:(oF' 0x98aa4%Z)) (ltac:(oD' 0x98aa4%Z)) ltac:(cond_compute).
stepLD8 (ltac:(oF' 0x98aa8%Z)) (ltac:(oD' 0x98aa8%Z)) (Z_to_bv 64 0x33b1c).
stepn (ltac:(oF' 0x98aac%Z)) (ltac:(oD' 0x98aac%Z)).
stepjr (ltac:(oF' 0x98ab0%Z)) (ltac:(oD' 0x98ab0%Z)) (Z_to_bv 64 0x33b1c) ltac:(gres; reflexivity). vnorm.
stepn (ltac:(oF' 0x33b1c%Z)) (ltac:(oD' 0x33b1c%Z)). sp_renorm.
stepST (ltac:(oF' 0x33b20%Z)) (ltac:(oD' 0x33b20%Z)) (Z_to_bv 64 (bv_unsigned sp - 56)) (Z_to_bv 64 0x98ab4) ltac:(sok_stack SOK).
stepST (ltac:(oF' 0x33b24%Z)) (ltac:(oD' 0x33b24%Z)) (Z_to_bv 64 (bv_unsigned sp - 64)) (Z_to_bv 64 0xaf1d0) ltac:(sok_stack SOK).
stepn (ltac:(oF' 0x33b28%Z)) (ltac:(oD' 0x33b28%Z)).
stepn (ltac:(oF' 0x33b2c%Z)) (ltac:(oD' 0x33b2c%Z)).
stepn (ltac:(oF' 0x33b30%Z)) (ltac:(oD' 0x33b30%Z)).
stepLBU (ltac:(oF' 0x33b34%Z)) (ltac:(oD' 0x33b34%Z)) (Z_to_bv 8 0) ltac:(rewrite v_addi_0; rdn_by Mcomp).
stepn (ltac:(oF' 0x33b38%Z)) (ltac:(oD' 0x33b38%Z)).
stepb_tk (ltac:(oF' 0x33b3c%Z)) (ltac:(oD' 0x33b3c%Z)) ltac:(cond_compute).
stepn (ltac:(oF' 0x33b48%Z)) (ltac:(oD' 0x33b48%Z)).
stepn (ltac:(oF' 0x33b4c%Z)) (ltac:(oD' 0x33b4c%Z)).
stepn (ltac:(oF' 0x33b50%Z)) (ltac:(oD' 0x33b50%Z)).
stepST (ltac:(oF' 0x33b54%Z)) (ltac:(oD' 0x33b54%Z)) (Z_to_bv 64 0xb6228) (Z_to_bv 64 1) ltac:(sok_data).
change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
stepn (ltac:(oF' 0x33b58%Z)) (ltac:(oD' 0x33b58%Z)).
stepLD8 (ltac:(oF' 0x33b5c%Z)) (ltac:(oD' 0x33b5c%Z)) (Z_to_bv 64 0x988ec).
stepb_ft (ltac:(oF' 0x33b60%Z)) (ltac:(oD' 0x33b60%Z)) ltac:(cond_compute).
stepn (ltac:(oF' 0x33b64%Z)) (ltac:(oD' 0x33b64%Z)).
stepn (ltac:(oF' 0x33b68%Z)) (ltac:(oD' 0x33b68%Z)).
stepn (ltac:(oF' 0x33b6c%Z)) (ltac:(oD' 0x33b6c%Z)).
stepLD8 (ltac:(oF' 0x33b70%Z)) (ltac:(oD' 0x33b70%Z)) (Z_to_bv 64 0xb5ef8).
stepn (ltac:(oF' 0x33b74%Z)) (ltac:(oD' 0x33b74%Z)).
stepret (ltac:(oF' 0x988ec%Z)) (ltac:(oD' 0x988ec%Z)) (0x33b78 : word) ltac:(bveq).
stepn (ltac:(oF' 0x33b78%Z)) (ltac:(oD' 0x33b78%Z)).
stepn (ltac:(oF' 0x33b7c%Z)) (ltac:(oD' 0x33b7c%Z)).
stepLD8 (ltac:(oF' 0x33b80%Z)) (ltac:(oD' 0x33b80%Z)) (Z_to_bv 64 0).
stepb_tk (ltac:(oF' 0x33b84%Z)) (ltac:(oD' 0x33b84%Z)) ltac:(cond_compute).
stepLD8 (ltac:(oF' 0x33b9c%Z)) (ltac:(oD' 0x33b9c%Z)) (Z_to_bv 64 0x98ab4).
stepLD8 (ltac:(oF' 0x33ba0%Z)) (ltac:(oD' 0x33ba0%Z)) (Z_to_bv 64 0xaf1d0).
stepn (ltac:(oF' 0x33ba4%Z)) (ltac:(oD' 0x33ba4%Z)). sp_renorm.
stepret (ltac:(oF' 0x33ba8%Z)) (ltac:(oD' 0x33ba8%Z)) (0x98ab4 : word) ltac:(bveq).
stepn (ltac:(oF' 0x98ab4%Z)) (ltac:(oD' 0x98ab4%Z)).
stepb_ft (ltac:(oF' 0x98ab8%Z)) (ltac:(oD' 0x98ab8%Z)) ltac:(cond_compute).
stepLD8 (ltac:(oF' 0x98abc%Z)) (ltac:(oD' 0x98abc%Z)) (Z_to_bv 64 0x98b38).
stepLD8 (ltac:(oF' 0x98ac0%Z)) (ltac:(oD' 0x98ac0%Z)) code.
stepLD8 (ltac:(oF' 0x98ac4%Z)) (ltac:(oD' 0x98ac4%Z)) s1v.
stepn (ltac:(oF' 0x98ac8%Z)) (ltac:(oD' 0x98ac8%Z)). sp_renorm.
stepn (ltac:(oF' 0x98acc%Z)) (ltac:(oD' 0x98acc%Z)).
stepret (ltac:(oF' 0x98a80%Z)) (ltac:(oD' 0x98a80%Z)) (0x98b38 : word) ltac:(bveq).
stepn (ltac:(oF' 0x98b38%Z)) (ltac:(oD' 0x98b38%Z)).
apply mst_refl.
- repeat split; gres; try reflexivity.
Qed.
End SE.
End FPX_1.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
