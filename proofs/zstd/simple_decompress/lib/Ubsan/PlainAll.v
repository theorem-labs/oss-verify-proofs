(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import ITree Nodes.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import Prog.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib Require Import TopLevel.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require PlainClosed RZ_huf_1x RZ_huf_4x RZ_huf_wkspc RZ_hft_x1 RZ_hft_x2 RZ_hft_rstats RZ_hft_fdec
  RF_fse_rd_err RZ_hft_bdt RZ_hft_bitinit RZ_hft_initds RZ_seq_default RZ_seq_split RZ_seq_long RZ_seq_execend RZ_seq_execsplit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem huf_rstats_closed : RZ_hft_rs_iface.huf_rstats_stmt.
Proof.
  exact (RZ_hft_rstats.huf_rstats_proof
           (RZ_hft_fdec.fse_dec_proof RF_fse_rd_err.fse_read_body_any_proof RZ_hft_bdt.fse_bdt_proof
                                      RZ_hft_bitinit.fse_bit_init_proof RZ_hft_initds.fse_initds_proof)).
Qed.

Theorem plain_impl_closed : forall (en : ExecEntry) (inp : ProcInput),
    valid_entry (mkImage usegs u_init_pc u_phdrs) en inp ->
    valid_input_either inp ->
    impl usegs (at_node usegs) (Prog.prog usegs UREAD_STAGE inp en) (epost (fun (_ : unit) (_ : machine_state) => True))
         (ms0 usegs u_init_pc u_phdrs en inp).
Proof.
  exact (PlainClosed.plain_closed_of_lib RZ_huf_1x.huf_1x_closed RZ_huf_4x.huf_4x_closed
           (RZ_huf_wkspc.huf_1x1_wksp_of_tbl (RZ_hft_x1.huf_rdx1_proof huf_rstats_closed))
           (RZ_huf_wkspc.huf_4x_wksp_of_tbl (RZ_hft_x1.huf_rdx1_proof huf_rstats_closed) (RZ_hft_x2.huf_rdx2_proof huf_rstats_closed))
           (RZ_seq_default.zd_seq_default_proof RZ_seq_execend.zd_execend_proof)
           (RZ_seq_split.zd_seq_split_proof RZ_seq_execend.zd_execend_proof RZ_seq_execsplit.zd_execend_split_proof)
           (RZ_seq_long.zd_seq_long_proof RZ_seq_execend.zd_execend_proof RZ_seq_execsplit.zd_execend_split_proof)).
Qed.
