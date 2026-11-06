(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-31: the A' start-up witness for the cf layer's Printf cells (field round 3,
   YG0ncf.v pf_cells_cf) at main entry, where the driver converts AR to ARcf (lib/A/PresetD1pAPf.v: W = AD2i.W1 ..,
   ly = AD1g.ly0 ch E model, mem = FULL). Proves no function (start-up facts). The pattern is lib/A/AD2iExhErrb.v's.
   THE TWO CELLS (CfImgA.v): SanitizerToolName at cf_toolname_cell 0xa3ed8 holds cf_toolname_val 0x20443 (the address of
   "AddressSanitizer" that AsanInitInternal stores), and PrintfAndReportCallback at cf_pfcb_cell 0x13cbd0 holds
   cf_pfcb_val 0x55d0c (AppendToErrorMessageBuffer, which AsanInitInternal passes to SetPrintfAndReportCallback).
   THE TABLE ROWS (lib/A/AB01.v, the 50 hand-off states): every state carries an 8-byte KWord at each cell with that
   value; lib/A/PresetImg_su_tool.v su_tool_cell_A reads the first by kn_read, lib/A/PresetImg_su_printf.v
   presetA_su_printf_handoff finds the second as a kentry. hs_pf_A checks both cells in all 50 states with
   AD1g.xcell (kn_read of the 8 bytes at the literal address, compared with the literal value).
   AD1g.xcell_sound turns it into cell_holds at AD1g.rd = aview TSEGS HID FULL (cs_ok co_know), and
   AD2iExhErrb.rd_ext_W with YG0scf.pf_cells_cf_ext carries the two cells to aview (w_H W') for every W' >= W1.
   main_pf_cells_A is PresetD1pA.H_start_pf_A's conclusion; lib/A/PresetD1pAPfC.v proves the row from it. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.omx_clap_core.fuzz_preset.images Require Import Asan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK00 YK04 YA0i YA0n YK0c YK0d YK0e YK0f YK09 YA01 YA0c YA0e YA0d YA02 YA0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB12 AB1h AB13 AB01 AF0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0f YG0v YG0n YM05 YGcfNames YG0ncf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0scf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AD1g AD2i CfImgA AD2iExhErrb.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Import AX2. Import AX2B. Import AX2S. Import APC. Import APG. Import APSG.
Open Scope Z_scope.

#[local] Notation TNC := (@cf_toolname_cell CfImgA.CfImg_A).
#[local] Notation TNV := (@cf_toolname_val CfImgA.CfImg_A).
#[local] Notation PCC := (@cf_pfcb_cell CfImgA.CfImg_A).
#[local] Notation PCV := (@cf_pfcb_val CfImgA.CfImg_A).

(* the two cells, checked in all 50 hand-off states *)
Definition PF_A : list acell := [z8 (ANum TNC) TNV; z8 (ANum PCC) PCV].
Lemma hs_pf_A : forallb (fun ch => forallb (AD1g.xcell ch) PF_A) HS_tfib_list = true.
Proof. vm_compute. reflexivity. Qed.

Section t. Context {fx : YK11.FPState}.
Variable B : asyms.
Hypothesis HB : TfibSyms B.
Variables (sp : word) (rdraw : EntryDraw) (brk : word) (inp : ProcInput).
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv (in_argv inp).
Variable h : nat.
Variables (ch : acs) (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis Hch : HS_tfib h = Some ch.
#[local] Notation argv := (in_argv inp).
#[local] Notation envp := (in_envp inp).
#[local] Notation uid := (in_uid inp).
#[local] Notation hw := (in_hwcap inp).
#[local] Notation SINV := (YA02.SINV0 TSEGS TPH sp rdraw brk argv envp uid hw).
#[local] Notation argH := (YA02.argH0 TPH sp rdraw argv envp uid hw).
#[local] Notation TOP := (YA02.TOP sp).
#[local] Notation LIM := YA02.LIMIT.
Hypothesis HC : cs_ok TSEGS TFIB LIM TOP SINV argH (in_fs inp) E ch R FULL model.
Context {rc : YM05.RunCeil}.
Hypothesis H1_8 : forall a : Z, YG0f.in_band_rw a ->
  AD2i.H1 sp rdraw inp ch E model (Z_to_bv 64 a) = AD2i.H1 sp rdraw inp ch E model (Z_to_bv 64 (a - a mod 8)).
#[local] Notation W1 := (AD2i.W1 sp rdraw inp Hsp Hva ch E model H1_8).
#[local] Notation ly := (AD1g.ly0 ch E model).

(* Printf's two cells at every W' >= W1: PresetD1pA.H_start_pf_A's conclusion at these binders *)
Theorem main_pf_cells_A : forall W' : world TSEGS, wle W1 W' ->
  pf_cells_cf (ci := CfImgA.CfImg_A) B ly (aview TSEGS (w_H W') FULL).
Proof.
intros W' L.
pose proof (proj1 (forallb_forall _ _) hs_pf_A ch (HS_tfib_In h ch Hch)) as K.
unfold PF_A in K. cbn [forallb] in K. apply andb_prop in K as [KT K]. apply andb_prop in K as [KP _].
assert (X : rd_ext (AD1g.rd sp rdraw inp ch E FULL model) (aview TSEGS (w_H W') FULL))
  by (eapply AD2iExhErrb.rd_ext_W; exact L).
apply (YG0scf.pf_cells_cf_ext B ly _ _ X).
split; apply (AD1g.xcell_sound B HB sp rdraw brk inp h ch E R FULL model Hch HC); assumption.
Qed.
End t.
