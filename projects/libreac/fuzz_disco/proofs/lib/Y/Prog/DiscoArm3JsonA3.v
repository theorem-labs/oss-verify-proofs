(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_stamp_headamp on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACbf.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACf6.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v, with its module paths and module names changed; 481 of its 517 lines of code are new or changed and 1242 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoEntProE.v, with its module paths and module names changed; 57 of its 93 lines of code are new or changed and 481 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/DiscoArm3Tail.v; 63 of its 96 lines of code are new or changed and 60 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0p YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC1g YC44 YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntSeatStmt DiscoArm3TailK DiscoArm3 DiscoArm3JsonModel DiscoArm3JsonCut DiscoArm3JsonMs
DiscoArm3JsonADefs.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_json_reader_model.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {LS : lib_shape}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Lemma ja3_present : forall (H : word -> bool) (m : word -> option byte) (nb : nat) p,
  (forall a, p <= a < p + Z.of_nat nb -> apresent H m a) ->
  exists A : list byte, length A = nb /\ garr8 SEGS (mrestrict H m) p (map (fun b : byte => bv_unsigned b) A).
Proof.
  intros H m nb. induction nb as [|nb IH]; intros p Hp.
  - exists []. split; [reflexivity|]. apply garr8_nil.
  - destruct (Hp p ltac:(lia)) as (Hh & b & Hb).
    destruct (IH (p + 1) ltac:(intros a Ha; apply Hp; lia)) as (A & HA & HG).
    exists (b :: A). split; [cbn [length]; rewrite HA; reflexivity|]. cbn [map].
    assert (Hav : aview SEGS H m p = Some (bv_unsigned b)).
    { unfold aview, mbyte, mrestrict. rewrite Hh, Hb. reflexivity. }
    destruct (val_mem1_of_aview SEGS H m p (bv_unsigned b) Hav) as (Hv & Hr).
    exact (garr8_cons_x SEGS _ p _ _ Hv Hr HG).
Qed.

Lemma ja3_obj0 : forall buf (vpad : list byte),
  map (fun b : byte => bv_unsigned b) (slot_ser_defs.objs_bytes buf vpad [jobj_empty]) = repeat 0 144.
Proof. intros buf vpad. reflexivity. Qed.

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.

Theorem jA_S3 : jA_S3_stmt B MT XM_LIB RLO RHI tfib_K.
Proof.
intros cx h i n now op W0 c0 T0 T1 buf fin W c Hms.
destruct Hms as (HFROM & Hv).
unfold d_arm_at_pf, d_at in Hv.
destruct Hv as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & Hfrm0 & HBASE & HJ & HFR & Hk & Hnev & HMO & Hacc &
  Hi & Hn & Hnow & HRL & (R26 & R24 & R25 & R10 & R21 & R22 & R23) & (HSP1 & HTAB & HBUF & (HJF & HJO) & HZ) &
  HSP0 & HBODY).
assert (HCTX : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by exact (conj HBASE (conj HJ HFR)).
pose proof (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HCTX)
  as (GS16 & GSlo & GShi & GF4096 & GFceil & GFapp & GFoff & GF32 & GFpres & GFsh & GSTK & HAR3 & HFin3 & EFA3 & EFL3).
pose proof (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (GA1 & GA32).
unfold MFRAME in GA1. unfold LLVMF_STK in GSlo.
destruct (ja3_present (w_H W) mem3 4 (d_A cx + 444) ltac:(intros a Ha; apply GSTK; unfold LLVMF_STK; lia))
  as (vpad & Hvl & Hvg).
unfold jcur in HZ. rewrite Z.mul_0_r, Z.add_0_r in HZ.
apply SRr_ret. exists vpad.
unfold jobj_in, jcut. split; [exact HFROM|].
unfold d_arm_at_pf, d_at.
exists fq, ly3, S3, regs, mem3, md3, k, acc.
split; [unfold JA_RET2, OBJ_OFF; reflexivity|].
split; [exact Hfrm0|]. split; [exact HBASE|]. split; [exact HJ|]. split; [exact HFR|].
split; [exact Hk|]. split; [exact Hnev|]. split; [exact HMO|]. split; [exact Hacc|].
split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|].
split; [exact HRL|].
split.
{ split; [exact R26|]. split; [exact R24|]. split; [exact R25|].
  split; [exact R21|]. split; [exact R22 | exact R23]. }
split.
{ split; [exact HSP1|]. split; [exact HTAB|]. split; [exact HBUF|].
  split; [exact HJF|]. split; [lia|]. split; [lia|]. split; [reflexivity|]. split; [exact HJO|].
  cbn [app].
  split; [exact Hvl|]. split; [exact Hvg|].
  split; [|constructor; [reflexivity | constructor]].
  rewrite ja3_obj0. exact HZ. }
split; [exact HSP0 | exact HBODY].
Qed.

End h.
End f.
End d.
