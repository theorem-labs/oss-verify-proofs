(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/AD2iExhErrb.v, with its module paths changed; 14 lines of the source are left out. *)
(* Theorem Labs, 2026-10-30: the A' start-up witness for the cf layer's two machine-cell fields at main
   entry, where the driver converts AR to ARcf (lib/A/PresetD1pAPf.v: W = AD2i.W1 .., ly = AD1g.ly0 ch E model,
   mem = FULL). Proves no function (start-up facts).
   Taken from the kit's earlier lib/A/AD2iExhErrb.v, 2026-10-31: its main_exh_errb_cf_A (over the
   CasanR2 copy of the field text, which YGcfCellsInit.v no longer has) and main_errb_obj_local_A (local facts the row
   does not read) are REMOVED. The field form is now PresetD1pA.H_start_cells_A itself, proved in
   lib/A/PresetD1pAPfC.v (H_start_cells_A_holds) from main_exh_errb_cells_A below and the draft's
   YGcfInstBase.exh_cell_cf_init / errb_cells_cf_init.
   MEASURED, not assumed. The 56-byte object [cf_errbuf_obj, + 56) (CfImgA.v, 0xaa728) is .bss. The 31 exhausted
   bytes (RegionInfo + 128 c + 68, CfImgA.v cf_exh_off) are in the FIRST page of the RegionInfo array, which is in the
   anonymous map after the primary space (map eP 137439023104, AD1g.v), NOT .bss. In each of the 50 hand-off states
   (AB01.v), the only kentries that meet the object are KImg 0xaa728..0xaaeb8 and the segment's KWr (no start-up store
   reached it). The RegionInfo page entry is exactly KZero (eSp1 + 65536 + 2 ^ 37, 4096). hs_cells_A checks both ranges
   with AD1g.xzero (kn_zero or kn_zcover of TFIB_BSS, whose image bytes are 0 by AB13.v tfib_bss_rom).
   AD1g.xzero_sound turns it into range_zero at AD1g.rd = aview TSEGS HID FULL (cs_ok co_know / co_zero). Every W' with
   wle W1 W' hides a subset of H1, which is a subset of HID (AD2i.H1_sub). So aview_ext (YG0n.v) carries the zeros to
   aview (w_H W') (rd_ext_W).
   The theorems take ONLY Hch and HC (AD1g's xzero_sound needs nothing else), plus the H1_8 that W1 is built with.
   (1) main_cells_zero_A: the first RegionInfo page and the whole 56-byte object read 0 at every W' >= W1.
   (2) main_exh_errb_cells_A: the cell form, the premises of YGcfInstBase.exh_cell_cf_init / errb_cells_cf_init. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.omx_clap_core.fuzz_preset.images Require Import Asan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK00 YK04 YA0i YA0n YK0c YK0d YK0e YK0f YK09 YA01 YA0c YA0e YA0d YA02 YA0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB12 AB1h AB13 AB01 AF0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0f YG0v YG0n YM05 YGcfNames YGcfCellsInit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AD1g AD2i CfImgA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Import AX2. Import AX2B. Import AX2S. Import APC. Import APG. Import APSG.
Open Scope Z_scope.

#[local] Notation OBJ := (@cf_errbuf_obj CfImgA.CfImg_A).
#[local] Notation XO := (@cf_exh_off CfImgA.CfImg_A).

(* the two ranges, checked in all 50 hand-off states *)
Definition CELLS_A : list (aexp * Z) := [(ANum OBJ, 56); (ASp kRegionInfoOff, 4096)].
Lemma hs_cells_A : forallb (fun ch => forallb (AD1g.xzero ch) CELLS_A) HS_tfib_list = true.
Proof. vm_compute. reflexivity. Qed.

Lemma exh_off_A : 0 <= XO /\ XO + 128 * 31 < 4096.
Proof. change XO with 68. lia. Qed.

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

Lemma rd_ext_W : forall W' : world TSEGS, wle W1 W' ->
  rd_ext (AD1g.rd sp rdraw inp ch E FULL model) (aview TSEGS (w_H W') FULL).
Proof.
intros W' L. rewrite AD1g.rd_aview. apply aview_ext.
- exact (ho_H_off TSEGS TFIB TOP argH tfib_in_hull (YA02.top_ok0 sp Hsp) tfib_hull_ok
    (YA02.argH0_high TPH sp rdraw argv envp uid hw Hsp Hva) E ch model).
- intros a Ha. exact (AD2i.H1_sub sp rdraw inp ch E model a (L a Ha)).
Qed.

Theorem main_cells_zero_A : forall W' : world TSEGS, wle W1 W' ->
  range_zero B ly (aview TSEGS (w_H W') FULL) (ASp kRegionInfoOff, 4096) /\
  range_zero B ly (aview TSEGS (w_H W') FULL) (ANum OBJ, 56).
Proof.
intros W' L.
pose proof (proj1 (forallb_forall _ _) hs_cells_A ch (HS_tfib_In h ch Hch)) as K.
unfold CELLS_A in K. cbn [forallb] in K. apply andb_prop in K as [KO K]. apply andb_prop in K as [KR _].
pose proof (rd_ext_W W' L) as X.
split; apply (range_zero_ext B ly _ _ _ X); apply (AD1g.xzero_sound B HB sp rdraw brk inp h ch E R FULL model Hch HC);
  assumption.
Qed.

(* the cell form: the premises of the draft's YGcfInstBase.exh_cell_cf_init and errb_cells_cf_init *)
Theorem main_exh_errb_cells_A : forall W' : world TSEGS, wle W1 W' ->
  (forall c, 1 <= c <= 31 ->
     cell_holds B ly (aview TSEGS (w_H W') FULL) (z1 (aoff (ASp (kRegionInfoOff + 128 * c)) XO) 0)) /\
  cell_holds B ly (aview TSEGS (w_H W') FULL) (z8 (ANum OBJ) 0) /\
  cell_holds B ly (aview TSEGS (w_H W') FULL) (z8 (ANum (OBJ + 16)) 0) /\
  cell_holds B ly (aview TSEGS (w_H W') FULL) (z8 (ANum (OBJ + 32)) 0) /\
  cell_holds B ly (aview TSEGS (w_H W') FULL) (z8 (ANum (OBJ + 40)) 0) /\
  cell_holds B ly (aview TSEGS (w_H W') FULL) (z8 (ANum (OBJ + 48)) 0).
Proof.
intros W' L. destruct (main_cells_zero_A W' L) as [ZR ZO]. destruct exh_off_A as [O1 O2].
split; [exact (@exh_bytes_zero CfImgA.CfImg_A B ly _ O1 O2 ZR) | exact (@errb_words_zero CfImgA.CfImg_A B ly _ ZO)].
Qed.
End t.
