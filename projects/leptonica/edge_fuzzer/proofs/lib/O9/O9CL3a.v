(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require ZArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require StackLayout.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From OSSVerify.leptonica.edge_fuzzer.images Require Plain.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require StartupTac.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require RefMemcpyLib.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica Require SumWalkTac.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica Require SumSpecs.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica Require WalksLib.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Reloc Require Reloc.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica Require RelocLept.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica.OL Require CmapFill.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.O9 Require O9Kit.
Module O9CmapFill.
Import Stdlib.ZArith.ZArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.Riscv.Decode.
Import LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.leptonica.edge_fuzzer.images.Plain.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.StartupTac.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.RefMemcpyLib.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica.SumWalkTac.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica.SumSpecs.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica.WalksLib.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Reloc.Reloc.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica.RelocLept.
Import O9Kit.
(* [comment removed for export] *)











Import O9Kit.O9Reloc. Import O9Kit.O9RelocCode. Import O9Kit.O9RelocSites. Import O9Kit.O9RelocImg. Import O9Kit.O9RelocOL.
Import ListNotations.
Open Scope bv_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section VPORT.
Context {fx : FPState}.
Definition CMAP_CLOB : list nat := [10; 11; 12; 13; 14; 15; 16; 21; 23]%nat.
Section CF.
Variable M : word -> option byte.
Variable rom : word -> option byte.
Variables cmap dp nc arr nalloc : Z.
Variable bs : list byte.
#[local] Notation data := (dp - 3)%Z (only parsing).
Hypothesis Hcmap : (1 <= cmap /\ cmap + 24 <= 2 ^ 64)%Z.
Hypothesis Hnc : (1 <= nc <= 256)%Z.
Hypothesis Hnal : (nc <= nalloc <= 256)%Z.
Hypothesis Harr : (1 <= arr /\ arr + 4 * nalloc <= 2 ^ 64)%Z.
Hypothesis Hdat : (3 <= dp /\ dp - 3 + 4 * nc <= 2 ^ 64)%Z.
Hypothesis Carr : rdn SEGS M (Z_to_bv 64 cmap) 8 = Some (Z_to_le_bytes 8 arr).
Hypothesis Cnal : rdn SEGS M (Z_to_bv 64 (cmap + 12)) 4 = Some (Z_to_le_bytes 4 nalloc).
Hypothesis Cn0 : rdn SEGS M (Z_to_bv 64 (cmap + 16)) 4 = Some (Z_to_le_bytes 4 0).
Hypothesis Dbs : rdn SEGS M (Z_to_bv 64 (dp - 3)) (Z.to_nat (4 * nc)) = Some bs.
Hypothesis SOKa : store_ok SEGS M (Z_to_bv 64 arr) (Z.to_nat (4 * nalloc)) = true.
Hypothesis SOKc : store_ok SEGS M (Z_to_bv 64 cmap) 24 = true.
Hypothesis A_ca : (cmap + 24 <= arr \/ arr + 4 * nalloc <= cmap)%Z.
Hypothesis A_cd : (cmap + 24 <= dp - 3 \/ dp - 3 + 4 * nc <= cmap)%Z.
Hypothesis A_ad : (arr + 4 * nalloc <= dp - 3 \/ dp - 3 + 4 * nc <= arr)%Z.
Lemma lez8 : forall z, (0 <= z < 2 ^ 64)%Z -> bytes_le_to_Z (Z_to_le_bytes 8 z) = bv_unsigned (Z_to_bv 64 z).
Proof. rl_tail (@CmapFill.lez8). Qed.

End CF.

Theorem cmapfill_contract :
  SSP.sum_contract SEGS (SSP.spec_cmapfill 0x660d8 0x65fdc 9 21 3 23 [(8%nat, 4%Z); (20%nat, 4%Z)] CMAP_CLOB).
Proof. rl_tail (@CmapFill.cmapfill_contract fx o9_reloc o9_code_ol). Qed.

End VPORT.
End O9CmapFill.

From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica Require W2Lib.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica.OL Require MaxIndex.
Module O9MaxIndex.
Import Stdlib.ZArith.ZArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.Riscv.Decode.
Import LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.leptonica.edge_fuzzer.images.Plain.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.StartupTac.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.RefMemcpyLib.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica.SumWalkTac.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica.SumSpecs.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica.WalksLib.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica.W2Lib.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Reloc.Reloc.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica.RelocLept.
Import O9Kit.
(* [comment removed for export] *)











Import O9Kit.O9Reloc. Import O9Kit.O9RelocCode. Import O9Kit.O9RelocSites. Import O9Kit.O9RelocImg. Import O9Kit.O9RelocOL.
Import ListNotations.
Open Scope bv_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section VPORT.
Context {fx : FPState}.
Theorem maxindex_contract : SSP.sum_contract SEGS (SSP.spec_maxindex 0x6639c 144).
Proof. rl_tail (@MaxIndex.maxindex_contract fx o9_reloc o9_code_ol o9_sites_ol). Qed.

End VPORT.
End O9MaxIndex.

From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica.OL Require PadBits.
Module O9PadBits.
Import Stdlib.ZArith.ZArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.Riscv.Decode.
Import LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.leptonica.edge_fuzzer.images.Plain.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.StartupTac.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.RefMemcpyLib.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica.SumWalkTac.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica.SumSpecs.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica.WalksLib.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Reloc.Reloc.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica.RelocLept.
Import O9Kit.
(* [comment removed for export] *)











Import O9Kit.O9Reloc. Import O9Kit.O9RelocCode. Import O9Kit.O9RelocSites. Import O9Kit.O9RelocImg. Import O9Kit.O9RelocOL.
Import ListNotations.
Open Scope bv_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section VPORT.
Context {fx : FPState}.
Section PB.
Variable M : word -> option byte.
Variable rom : word -> option byte.
Variables pix w h d wpl data sp : Z.
Variables ra s0v s1v s2v : word.
Hypothesis Hpix : (1 <= pix /\ pix + 12 <= 2 ^ 64)%Z.
Hypothesis Hpix64 : (pix + 64 <= 2 ^ 64)%Z.
Hypothesis Rw : (0 <= w < 2 ^ 32)%Z.
Hypothesis Rh : (0 <= h < 2 ^ 32)%Z.
Hypothesis Hw : (1 <= w <= 20000)%Z.
Hypothesis Hh : (1 <= h <= 20000)%Z.
Hypothesis Hd : (d = 1 \/ d = 2 \/ d = 4 \/ d = 8 \/ d = 16 \/ d = 24)%Z.
Hypothesis Hsp : (48 <= sp /\ sp < 2 ^ 64)%Z.
Hypothesis Hra : ret_ok ra.
Hypothesis Cw : rdn SEGS M (Z_to_bv 64 pix) 4 = Some (Z_to_le_bytes 4 w).
Hypothesis Ch : rdn SEGS M (Z_to_bv 64 (pix + 4)) 4 = Some (Z_to_le_bytes 4 h).
Hypothesis Cd : rdn SEGS M (Z_to_bv 64 (pix + 8)) 4 = Some (Z_to_le_bytes 4 d).
Hypothesis Cwpl : rdn SEGS M (Z_to_bv 64 (pix + 16)) 4 = Some (Z_to_le_bytes 4 wpl).
Hypothesis Cdata : rdn SEGS M (Z_to_bv 64 (pix + 56)) 8 = Some (Z_to_le_bytes 8 data).
Hypothesis Hwpl : (0 <= wpl <= 20000)%Z.
Hypothesis Hdata : (1 <= data /\ data < 2 ^ 64)%Z.
Hypothesis HR : (data + 4 * (wpl * h) <= 2 ^ 64)%Z.
Hypothesis SOKr : store_ok SEGS M (Z_to_bv 64 data) (Z.to_nat (4 * (wpl * h))) = true.
Hypothesis FR : disj_apart data (4 * (wpl * h)) (sp - 48) 48.
Hypothesis SOKf : store_ok SEGS M (Z_to_bv 64 (sp - 48)) 48 = true.
Hypothesis FP12 : disj_apart pix 12 (sp - 48) 48.
Hypothesis FP : disj_apart pix 64 (sp - 48) 48.
Definition M1 : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes M (Z_to_bv 64 (sp - 8)) (word_to_le_bytes 8 ra))
                           (Z_to_bv 64 (sp - 16)) (word_to_le_bytes 8 s0v))
                   (Z_to_bv 64 (sp - 24)) (word_to_le_bytes 8 s1v))
           (Z_to_bv 64 (sp - 32)) (word_to_le_bytes 8 s2v).
Definition M2g (vw vh : word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes M1
      (Z_to_bv 64 (sp - 36)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
      (Z_to_bv 64 (sp - 40)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
      (Z_to_bv 64 (sp - 44)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
      (Z_to_bv 64 (sp - 36)) (word_to_le_bytes 4 vw))
      (Z_to_bv 64 (sp - 40)) (word_to_le_bytes 4 vh))
      (Z_to_bv 64 (sp - 44)) (word_to_le_bytes 4 (Z_to_bv 64 d)).
Definition M2 : word -> option byte := M2g (Z_to_bv 64 w) (Z_to_bv 64 h).
Lemma lez4 : forall z, (0 <= z < 2 ^ 32)%Z -> bytes_le_to_Z (Z_to_le_bytes 4 z) = bv_unsigned (Z_to_bv 64 z).
Proof. rl_tail (@PadBits.lez4). Qed.

#[local] Notation RS := (4 * (wpl * h))%Z (only parsing).
Definition Inv (Mi : word -> option byte) : Prop :=
    (forall x : word, (bv_unsigned x < data \/ data + RS <= bv_unsigned x)%Z -> Mi x = M2 x)
    /\ mem_grows M2 Mi.
Lemma M2_grows : mem_grows M M2.
Proof. rl_tail (@PadBits.M2_grows M w h d sp ra s0v s1v s2v). Qed.

Lemma M2g_outside : forall vw vh (x : word),
    (bv_unsigned x < sp - 48 \/ sp <= bv_unsigned x)%Z -> M2g vw vh x = M x.
Proof. rl_tail (@PadBits.M2g_outside M d sp ra s0v s1v s2v Hsp). Qed.

Theorem padbits_run : forall regs,
    (d <> 24)%Z -> (wpl = (w * d + 31) / 32)%Z ->
    getr regs 1 = ra -> getr regs 2 = Z_to_bv 64 sp -> getr regs 8 = s0v -> getr regs 9 = s1v -> getr regs 18 = s2v ->
    getr regs 10 = Z_to_bv 64 pix -> getr regs 11 = Z_to_bv 64 0 ->
    exists regs' M',
      msteps SEGS (mkst regs (0x63e88 : word) M rom) (mkst regs' ra M' rom)
      /\ Inv M'
      /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 2 = Z_to_bv 64 sp
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v
      /\ regs_agree (fun x : reg => In x [1; 2; 8; 9; 10; 11; 12; 13; 14; 18]%list) regs regs'.
Proof. rl_tail (@PadBits.padbits_run fx o9_reloc o9_code_ol o9_sites_ol o9_lept o9_img_ol M rom pix w h d wpl data sp ra s0v s1v s2v Hpix Hpix64 Rw Rh Hw Hh Hd Hsp Hra Cw Ch Cd Cwpl Cdata Hwpl Hdata HR SOKr FR SOKf FP12 FP). Qed.

End PB.

Definition padbits24_L_ok (L : SSP.ls_addrs) : Prop :=
  (SSP.ls_entry L = 0x5ce08 /\ SSP.ls_sev_got L = 0xee570 /\ In 0x151f1 (SSP.ls_fmts1 L)
   /\ (0 <= SSP.ls_img_lo L <= 0x151f1 /\ 0x1747a <= SSP.ls_img_hi L <= SSP.ls_sp_lo L)
   /\ 0 <= SSP.ls_frame L)%Z.
Theorem padbits24_contract : forall L : SSP.ls_addrs,
  padbits24_L_ok L ->
  SSP.sum_contract SEGS (SSP.spec_lept_stderr_s1 L) ->
  SSP.sum_contract SEGS (SSP.spec_padbits24 0x63e88 (48 + SSP.ls_frame L) L).
Proof.
  intros L HL HC.
  pose proof (@PadBits.padbits24_contract fx o9_reloc o9_code_ol o9_sites_ol o9_lept o9_img_ol L) as RLT.
  unfold PadBits.padbits24_L_ok in RLT. unfold padbits24_L_ok in HL.
  rl_bare_in RLT.
  apply RLT; [ | exact HC].
  destruct HL as (HLe & HLsg & HLfmt & HLimg & HLfr). repeat split; try assumption; lia.
Qed.

End VPORT.
End O9PadBits.
