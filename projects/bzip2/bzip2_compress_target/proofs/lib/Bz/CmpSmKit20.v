(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import SegsS0.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCStream BzCState BzCMtf BzArrD CmpMem CmpCut CmpCutSM CmpCutSmA CmpCutSmB CmpHmKit BzCFactsGm BzCSmF1 BzCFactsSmB BzCFactsSmB2 CmpSmKit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Musl Require Import MuslStr.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require ZBridge.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge.Bytes.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpSmKit2 CmpCut0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Lemma cimg_transportK0 : forall I W m m' sv, I = S0C ->
  cimg_mem I m sv -> munch W m m' -> wmono (ci_segs I) m m' -> w_img_apartK (ci_hi I) W -> cimg_mem I m' sv.
Proof.
  (intros I W m m' sv HI; cps_intros (H1 & H2 & H3 & H4); intros MU WM AP).
  assert (R : IMG_LO3 <= ci_got I /\ ci_got I + 32 <= ci_hi I /\ IMG_LO3 <= ci_stderrp I /\ ci_stderrp I + 8 <= ci_hi I /\
              IMG_LO3 <= ci_crc I /\ ci_crc I + Z.of_nat (cells_size (CB 1024 BzTables.bz_crc_table_bytes :: ci_crcx I)) <= ci_hi I).
  { subst I; cbn; unfold IMG_LO3; lia. }
  (* [comment removed for export] *)
  cps_destruct R as (R1 & R2 & R3 & R4 & R5 & R6).
  unfold cimg_mem. split; [|split; [|split]].
  1-3: (eapply rw_cells_transport; [eassumption | exact MU | exact WM | apply (w_img_apartK_disjoint (ci_hi I)); [exact AP | cbn; lia | cbn; lia]]).
  eapply rw_cells_transport; [exact H4 | exact MU | exact WM | apply (w_img_apartK_disjoint (ci_hi I)); [exact AP | exact R5 | exact R6]].
Qed.

End ACeilS1.
