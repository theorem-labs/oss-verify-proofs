(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Arr Bytes ZBridge Tac InitMem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AImg ABase RtCells ABytes AMalloc_iface AHarness_iface AKit FsKit AH_fse_kit AH_fse_calls AH_fse_Eiface.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import ShadowTac.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import FseWalkKitF.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_orc_old ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_k12.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.slia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.slia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.flia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.flia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange_nonneg ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_nonneg_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.solve_load_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.word_eq_tac_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common.FseWalkKit.simpl_arr_sizes_fwk_k12.
(* [comment removed for export] *)

Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac solve_load ::= first [ solve_load_guarded | solve_load_image ].
Local Ltac solve_store ::= solve_store_guarded.
Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Theorem pE1_proof : pE1_stmt.
Proof.
unfold pE1_stmt.
intros RNG gp tp s0 s2 s3 s4 s5 s6 s7 s9 s10 FR fc x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m SPA F P tl B j16
SPA0 SPAH SPAK F2048 FH FC FRA SH MI RT RFRA RSF RI.
pose proof (ablk_lin _ _ FH) as (FH1 & FH2 & FH3 & FH4). unfold AIMG_HI in FH1.
pose proof atop_range as ATR. unfold KHIGH in SPAK.
Local Ltac2 Set LiaHints.tbl := fun () => "00X0>10028172029.8911801586693.8811801586693.8911805467289.7111805467289.7212212342311.7013245442551.631687698010.72 22026868477.8922700267513.9024205896189.8924869599638.8425345210196.5526872077798.712699033477.63 27807894880.6229786411260.5535499906471.7035895327997.8937497880812.8838525121917.8939665081360.7239926726630.7241229298317.8942985490938.7144506359019.8344527916794.7150187749100.7250620450074.7250631710663.7155191925324.8455330730406.7056043686656.6956854914829.7059378787372.7159545181270.7059999450034.7263478620285.897381600893.89 7507164690.71 00000600700800900:00;00<00B00H00O00U00V00W00X00^00_00`00a00g01201801901:01;01A01B01H01I01O01P01Q01W02202802902:02E02K02Q02\S4BSF1SSSSSSS4BSF1S4BSF1S3FH21HS4BSF1SSSS4BSF1SSSS4BSF1S4SPAK4BSF2S4BSF1SSFS4BSF1SS4BSF2SS4BSF2SSS4BSF2S5F20483FH13FH33ATR1H2H02H4S4BSF1SSS4SPAK4BSF2S4BSF1S4BSF1S4SPAK4BSF2".
replace (shad F) with (Z.shiftr F 3 + ASHOFF) in RSF by (unfold shad; lia).
assert (BSF : 2147450880 <= Z.shiftr F 3 + ASHOFF /\ Z.shiftr F 3 + ASHOFF + 256 <= 17594333495296)
by (rewrite Z.shiftr_div_pow2 by lia; unfold ASHOFF; Z.div_mod_to_equations; lia).
destruct BSF as [BSF1 BSF2].
lazymatch goal with |- evtF _ _ ?Q _ => set (QQ := Q) end.
unfold FRA_E, SHF, FSH, ASHOFF in FRA, SH, RSF, BSF1, BSF2. unfold SHF, ASHOFF.
pose proof (munch_refl [(Z.shiftr F 3 + 2147450880, Z.shiftr F 3 + 2147450880 + 256)] m) as MU.
pose proof (wmono_refl asegs m) as WM.
zstep.
replace (Z_to_bv 64 (-8)) with (Z_to_bv 64 18446744073709551608) by (apply Z_to_bv_eqm; reflexivity).
zstep. zstep.
zstep. zstep.
zstep.
lazymatch goal with SHx : rw_cells asegs _ (Z.shiftr F 3 + 2147450880) _ |- _ => rw_split SHx 22%nat SHa SHr end.
rw_split SHr 1%nat SHb SHc.
pose proof (fse_rt_munch _ _ _ RT MU WM ltac:(cbn [above]; unfold AIMG_HI; split; [lia| exact I])) as RTN.
unfold fse_rt in RTN. destruct RTN as (RT1 & RT2 & RT3 & RT4 & RT5 & RT6 & RT7).
call (ss_f8_z RNG); [ first [ exact SHb | eassumption | lia | eapply rng_sub'; [exact RSF| lia] ] .. | ].
change (Z.to_nat 64) with 64%nat in POST. rw_join SHa POST SH1. rw_join SH1 SHc SH2. cbn [app] in SH2.
zstep.
zstep.
apply evtF_done. unfold QQ, FRA_E, SHF, FSH, ASHOFF.
do 15 eexists. split; [reflexivity|].
split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
exact SH2.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
