(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdHufFse.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk PropExec MState Frame.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit FseWalkMem MemRange ZdWalkKit ZdCellKit SepHide.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AZ_kit AZ_globals AZ_globalsR AZ_huf_iface AZ_hft_iface AZ_kx AZ_hft_initds AZ_hft_initds_fin
     AZ_fse_bitinit AZ_hft_dsym AZ_hft_fdec_defs AZ_hft_fdec_epi AZ_hft_fdec_close AZ_hft_fdec_nz AZ_hft_fdec_nt5.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC2. Context {rc : runConstT}.
Lemma nonfh : forall (RNG : footprint) (mA : amem) (SPV SPB lo DST cap SRC n WK wksz hs tl fast FF : Z) (tb : list Z) (src : list byte) (gp tp : word) (F : bvmap 5 word) (fc : bv 32),
  fdA_hyps RNG SPV SPB lo DST cap SRC n WK wksz (WK + 512) hs tl FF -> fdA_an RNG mA SPV SPB lo DST cap SRC n WK wksz (WK + 512) hs tl fast FF tb src -> fast = 0 ->
  fd_entK RNG (fd_qexit gp tp F fc mA SPV SPB lo DST cap FF) gp tp F fc mA SPV SPB lo DST cap SRC n hs WK wksz (WK + 512) FF 0xac2bc.
Proof.
  intros until fc. intros HY AN F0.
  Ltac plug HY AN F0 := first [ exact HY | exact AN | exact F0 | apply fd_qx | exact fse_bit_init_proofA | exact fse_initds_proofA | idtac ].
  eapply fd_nonfast_halfK; plug HY AN F0.
  all: first [ eapply nt_entry; plug HY AN F0 | eapply nt_entry0; plug HY AN F0 ].
Qed.
End CANSEC2.
