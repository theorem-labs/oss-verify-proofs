(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
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
From OssFuzzTheorems.leptonica.grayquant_fuzzer.images Require Ubsan.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require StartupTac.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require RefMemcpyLib.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require SumWalkTac.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require SumSpecs.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require WalksLib.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Reloc Require Reloc.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require RelocLept.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.VL Require CmapFill.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15Kit.
Module V15CmapFill.
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
Import OssFuzzTheorems.leptonica.grayquant_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.StartupTac.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.RefMemcpyLib.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.SumWalkTac.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.SumSpecs.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.WalksLib.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Reloc.Reloc.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.RelocLept.
Import V15Kit.
(* [comment removed for export] *)











Import V15Kit.V15Reloc. Import V15Kit.V15RelocCode. Import V15Kit.V15RelocSites. Import V15Kit.V15RelocImg. Import V15Kit.V15RelocVL.
Import ListNotations.
Open Scope bv_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Section VPORT.
Context {fx : FPState}.
Definition ULITS : list (nat * Z) := [(23%nat, 0%Z); (9%nat, 4%Z); (22%nat, 4%Z)].
Definition UCLOB : list nat := [5; 10; 11; 12; 13; 14; 15; 16; 17; 23]%nat.
Lemma lez8 : forall z, (0 <= z < 2 ^ 64)%Z -> bytes_le_to_Z (Z_to_le_bytes 8 z) = bv_unsigned (Z_to_bv 64 z).
Proof. rl_tail (@CmapFill.lez8). Qed.

Theorem cmapfill_contract :
  SSP.sum_contract SEGS (SSP.spec_cmapfill 0x19aa8 0x199cc 19 18 0 8 ULITS UCLOB).
Proof. rl_tail (@CmapFill.cmapfill_contract fx v15_reloc v15_code_vl). Qed.

End VPORT.
End V15CmapFill.

From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require W2Lib.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.VL Require MaxIndex.
Module V15MaxIndex.
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
Import OssFuzzTheorems.leptonica.grayquant_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.StartupTac.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.RefMemcpyLib.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.SumWalkTac.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.SumSpecs.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.WalksLib.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.W2Lib.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Reloc.Reloc.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.RelocLept.
Import V15Kit.
(* [comment removed for export] *)











Import V15Kit.V15Reloc. Import V15Kit.V15RelocCode. Import V15Kit.V15RelocSites. Import V15Kit.V15RelocImg. Import V15Kit.V15RelocVL.
Import ListNotations.
Open Scope bv_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Section VPORT.
Context {fx : FPState}.
Theorem maxindex_contract : SSP.sum_contract SEGS (SSP.spec_maxindex 0x19bb8 128).
Proof. rl_tail (@MaxIndex.maxindex_contract fx v15_reloc v15_code_vl v15_sites_vl). Qed.

End VPORT.
End V15MaxIndex.

From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.VL Require PadBits.
Module V15PadBits.
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
Import OssFuzzTheorems.leptonica.grayquant_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.StartupTac.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.RefMemcpyLib.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.SumWalkTac.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.SumSpecs.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.WalksLib.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Reloc.Reloc.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.RelocLept.
Import V15Kit.
(* [comment removed for export] *)











Import V15Kit.V15Reloc. Import V15Kit.V15RelocCode. Import V15Kit.V15RelocSites. Import V15Kit.V15RelocImg. Import V15Kit.V15RelocVL.
Import ListNotations.
Open Scope bv_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Section VPORT.
Context {fx : FPState}.
Section PB.
Variable M : word -> option byte.
Variable rom : word -> option byte.
Variables pix w h d wpl data sp : Z.
Variables ra s0v s1v s2v : word.
Hypothesis Hpix : (1 <= pix /\ pix + 12 <= 2 ^ 64)%Z.
Hypothesis Hpix64 : (pix + 64 <= 2 ^ 64)%Z.
Hypothesis ALpix : is_aligned pix 8.
Hypothesis Rw : (0 <= w < 2 ^ 32)%Z.
Hypothesis Rh : (0 <= h < 2 ^ 32)%Z.
Hypothesis Hw : (1 <= w <= 20000)%Z.
Hypothesis Hh : (1 <= h <= 20000)%Z.
Hypothesis Hd : (d = 1 \/ d = 2 \/ d = 4 \/ d = 8 \/ d = 16 \/ d = 24)%Z.
Hypothesis Hsp : (48 <= sp /\ sp < 2 ^ 64)%Z.
Hypothesis ALsp : is_aligned sp 16.
Hypothesis Hra : ret_ok ra.
Hypothesis Cw : rdn SEGS M (Z_to_bv 64 pix) 4 = Some (Z_to_le_bytes 4 w).
Hypothesis Ch : rdn SEGS M (Z_to_bv 64 (pix + 4)) 4 = Some (Z_to_le_bytes 4 h).
Hypothesis Cd : rdn SEGS M (Z_to_bv 64 (pix + 8)) 4 = Some (Z_to_le_bytes 4 d).
Hypothesis Cwpl : rdn SEGS M (Z_to_bv 64 (pix + 16)) 4 = Some (Z_to_le_bytes 4 wpl).
Hypothesis Cdata : rdn SEGS M (Z_to_bv 64 (pix + 56)) 8 = Some (Z_to_le_bytes 8 data).
Hypothesis Hwpl : (0 <= wpl <= 20000)%Z.
Hypothesis Hdata : (1 <= data /\ data < 2 ^ 64)%Z.
Hypothesis ALdata : is_aligned data 4.
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
      msteps SEGS (mkst regs (0x181ac : word) M rom) (mkst regs' ra M' rom)
      /\ Inv M'
      /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 2 = Z_to_bv 64 sp
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v
      /\ regs_agree (fun x : reg => In x [1; 2; 5; 6; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18]%list) regs regs'.
Proof. rl_tail (@PadBits.padbits_run fx v15_reloc v15_code_vl v15_sites_vl v15_lept v15_img_vl M rom pix w h d wpl data sp ra s0v s1v s2v Hpix Hpix64 ALpix Rw Rh Hw Hh Hd Hsp ALsp Hra Cw Ch Cd Cwpl Cdata Hwpl Hdata ALdata HR SOKr FR SOKf FP12 FP). Qed.

End PB.

Definition padbits24_L_ok (L : SSP.ls_addrs) : Prop :=
  (SSP.ls_entry L = 0x15520 /\ SSP.ls_sev_got L = 0x341f8 /\ In 0x109e6 (SSP.ls_fmts1 L)
   /\ (0 <= SSP.ls_img_lo L <= 0x109e6 /\ 0x10d27 <= SSP.ls_img_hi L <= SSP.ls_sp_lo L)
   /\ 0 <= SSP.ls_frame L)%Z.
Theorem padbits24_contract : forall L : SSP.ls_addrs,
  padbits24_L_ok L ->
  SSP.sum_contract SEGS (SSP.spec_lept_stderr_s1 L) ->
  SSP.sum_contract SEGS (SSP.spec_padbits24 0x181ac (48 + SSP.ls_frame L) L).
Proof.
  intros L HL HC.
  pose proof (@PadBits.padbits24_contract fx v15_reloc v15_code_vl v15_sites_vl v15_lept v15_img_vl L) as RLT.
  unfold PadBits.padbits24_L_ok in RLT. unfold padbits24_L_ok in HL.
  rl_bare_in RLT.
  apply RLT; [ | exact HC].
  destruct HL as (HLe & HLsg & HLfmt & HLimg & HLfr). repeat split; try assumption; lia.
Qed.

End VPORT.
End V15PadBits.
