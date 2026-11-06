(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.

From Stdlib Require Import ZArith NArith Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType StackLayout State Run Fs.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon Require Import FastWord ShapeAlg ShapeAlgCfg.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import AxLin AxState AxSys AxRun AxEntryRel AxModelRel AxFd AxTabs AxSumCk AxStart.
From OSSVerify.Proofs.openssl.bignum.lib.BgAxBdB Require Import BdBParams BdBHints.
Require OSSVerify.openssl.bignum.images.AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Open Scope Z_scope.

Local Notation CFG := (mkSpuriousCfg false true true true true true).
Local Notation LIM := target_alloc_limit.

Definition MAIN_PC : Z := 0x1edb20.

Definition HFS : list (Z * list hint) := (MAIN_PC, [HStop]) :: HF0.

Notation bdb_cert fin :=
  (start_cert BDB_SEGS BDB_PC BDB_PH target_alloc_limit (asum_ck bdb_tabs BDB_SEGS target_alloc_limit) fin (mk_htable HFS) FUEL_F) (only parsing).

Definition fin_main0 (B : AST) : bool := w_eqb (a_pc B) (wofZ MAIN_PC) && is_nilb (am_out (a_model B)).

Section Startup.
Variable POST : list (list byte) -> Fs.Fs -> config -> Prop.
Variable fin : AST -> bool.
Hypothesis Hfin_out : forall B, fin B = true -> am_out (a_model B) = [].

Hypothesis Hbridge : forall (fs0 : Fs.Fs) (B : AST), fin B = true ->
  forall ρ c, R BDB_SEGS amodel (MR BDB_SEGS fs0 ρ) LIM ρ B c ->
  forall T : TSet, (forall c', POST (dec_argvB ρ) fs0 c' -> realizes_cfg BDB_SEGS CFG c' T) -> realizes_cfg BDB_SEGS CFG c T.
Hypothesis Hcert : bdb_cert fin = true.

Theorem bdb_startup : forall (TT : list (list byte) -> TSet) (en : ExecEntry) (inp : ProcInput),
  valid_input inp ->
  valid_entry (mkImage BDB_SEGS BDB_PC BDB_PH) en inp ->
  (forall argv c, valid_argv argv -> POST argv (in_fs inp) c -> realizes_cfg BDB_SEGS CFG c (TT argv)) ->
  realizes_cfg BDB_SEGS CFG
    (init_config BDB_SEGS BDB_PC BDB_PH (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en) LIM inp)
    (TT (in_argv inp)).
Proof.
  pose proof (asum_ck_ok bdb_tabs BDB_SEGS BDB_PC CFG LIM bdb_img_ok bdb_tabs_ok bdb_cks_ok) as Hsum.
  assert (Hcfg2 : sc_alloc CFG = false) by reflexivity.
  exact (startup_sound BDB_SEGS BDB_PC BDB_PH CFG Hcfg2 LIM bdb_img_ok (asum_ck bdb_tabs BDB_SEGS LIM) Hsum
           POST fin Hfin_out Hbridge (mk_htable HFS) FUEL_F Hcert).
Qed.

End Startup.
