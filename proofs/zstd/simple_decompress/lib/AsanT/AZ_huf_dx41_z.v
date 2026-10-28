(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AZ_kit AZ_huf_iface AZ_huf_iface3 AZ_hufkit AZ_huf_reloadi AZ_huf_bitinit AZ_huf_fastargs
     AZ_huf_dx41 AZ_huf_dx41_4a AZ_huf_dx41_e AZ_huf_dx41_n0.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Warnings "-notation-for-abbreviation".

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Definition x41_fast_stmtA : Prop :=
  forall (RNG : footprint) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : amem)
         (SPV DST dcap SRC n DT tl rsv lo : Z) (src dtb : list byte),
    x41a_ctx SPV DST dcap SRC n DT tl rsv lo src dtb -> x41a_actx RNG m0 SPV DST dcap SRC n DT lo ->
    huf_nb_ok false dtb tl -> dst_hi dcap DST ->
    AZ_huf_dx41.x41_fast_stmt RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl lo src dtb.

(* [comment removed for export] *)
Theorem huf_4x1_proofB : bit_init_stmtA -> fast_args_stmt3A -> x41_fast_stmtA -> huf_4x1_stmtA.
Proof.
  intros BITINIT FASTARGS XFASTA.
  unfold huf_4x1_stmtA, huf_int_stmtA_at, APHUF_4X1.
  intros until dtb.
  intros (MI & STK & LO0 & LO & SPB & OUT & D0 & D1 & D2 & SRCB & SL & S0 & S1 & S2 & OS1 & OS2 & DJ1 & ARD & ARS & ART & AST & AZS & ARC & SPA)
         (DTB & DL & T0 & T1 & OS3 & DJ2 & ARODT & DTA) DT2 TL X2 NB.
  unfold HUF_DTABLE_BYTES in *.
  destruct AST as (KLO & RSTK & RI).
  destruct ARODT as (UDT & RDT & RDTS).
  assert (DSTA : dcap <= 0 \/ (DST + dcap <= 0x7fff7000 \/ 0x10007fff8000 <= DST)).
  { destruct (Z_lt_le_dec 0 dcap) as [Hd|Hd]; [| left; lia]. right.
    destruct (ARD Hd) as (ABD & _). unfold ablk, AIMG_HI, KLS, KHIGH in ABD |- *. lia. }
  assert (DHI : dst_hi dcap DST).
  { unfold dst_hi. intros Hd. destruct (ARD Hd) as (ABD & _). unfold ablk, AIMG_HI, KLS, KHIGH in ABD |- *. lia. }
  destruct (Z.eq_dec n 0) as [N0|N1].
  { subst n. replace (zlen src) with 0 by lia.
    destruct ART as (GOT & RIC & SHB & INI & LAY & REAL). unfold KHIGH in KLO.
    eapply AZ_huf_dx41_n0.x41_n0; first [exact GOT | exact SHB | exact UDT | exact RDTS | exact RDT | exact RI | exact RSTK | exact DSTA | exact DTA | exact DL | eassumption | lia]. }
  destruct (ARS ltac:(lia)) as (ABS & USRC & RSRC & RSRCS).
  destruct (nth_error dtb 3) as [b3|] eqn:DT3; [| apply nth_error_None in DT3; exfalso; lia].
  assert (CTX : x41a_ctx SPV DST dcap SRC n DT tl (bv_unsigned b3) lo src dtb).
  { pose proof (bv_unsigned_in_range 8 b3) as RB. unfold bv_modulus in RB. change (2 ^ Z.of_N 8) with 256 in RB.
    assert (EB : Z_to_bv 8 (bv_unsigned b3) = b3)
      by (apply bv_eq; rewrite Z_to_bv_unsigned; apply bv_wrap_small; apply bv_unsigned_in_range).
    unfold x41a_ctx. rewrite EB. unfold KHIGH in KLO. repeat split; try assumption; lia. }
  assert (ACTX : x41a_actx RNG m SPV DST dcap SRC n DT lo).
  { unfold x41a_actx. unfold KHIGH in KLO |- *.
    split; [exact USRC|]. split; [exact UDT|].
    split; [intros Hd; destruct (ARD Hd) as (_ & U & _); exact U|].
    split; [exact RSRC|]. split; [exact RSRCS|]. split; [exact RDT|]. split; [exact RDTS|].
    split; [intros Hd; destruct (ARD Hd) as (_ & _ & R & _); exact R|].
    split; [intros Hd; destruct (ARD Hd) as (_ & _ & _ & R); exact R|].
    split; [exact RSTK|]. split; [exact RI|]. split; [exact AZS|]. split; [exact ARC | exact ART]. }
  exact (AZ_huf_dx41_e.x41_entry RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV DST dcap SRC n DT tl (bv_unsigned b3) lo src dtb
           CTX ACTX DHI NB BITINIT FASTARGS
           (XFASTA RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV DST dcap SRC n DT tl (bv_unsigned b3) lo src dtb CTX ACTX NB DHI)
           t0 t1 t2 flags a6 a7 t3 t4 t5 t6 ltac:(lia) MI STK OUT SRCB DTB).
Qed.

(* [comment removed for export] *)
Theorem huf_4x1_proofA : x41_fast_stmtA -> huf_4x1_stmtA.
Proof. intros XF. exact (huf_4x1_proofB bit_init_proofA fast_args_proof3A XF). Qed.

End CANSEC1.
