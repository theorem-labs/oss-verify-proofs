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
From OSSVerify.Proofs.openssl.bignum.lib.BgAxBdA Require Import BdAParams BdAHints.
Require OSSVerify.openssl.bignum.images.Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Open Scope Z_scope.

Local Notation CFG := (mkSpuriousCfg false true true true true true).
Local Notation LIM := target_alloc_limit.

Definition MAIN_PC : Z := 0x1f2b34.

Definition HFS : list (Z * list hint) := (MAIN_PC, [HStop]) :: HF0.

Notation bda_cert fin :=
  (start_cert BDA_SEGS BDA_PC BDA_PH target_alloc_limit (asum_ck bda_tabs BDA_SEGS target_alloc_limit) fin (mk_htable HFS) FUEL_F) (only parsing).

Definition fin_main0 (B : AST) : bool := w_eqb (a_pc B) (wofZ MAIN_PC) && is_nilb (am_out (a_model B)).

Section Startup.
Variable POST : list (list byte) -> Fs.Fs -> config -> Prop.
Variable fin : AST -> bool.
Hypothesis Hfin_out : forall B, fin B = true -> am_out (a_model B) = [].

Hypothesis Hbridge : forall (fs0 : Fs.Fs) (B : AST), fin B = true ->
  forall ρ c, R BDA_SEGS amodel (MR BDA_SEGS fs0 ρ) LIM ρ B c ->
  forall T : TSet, (forall c', POST (dec_argvB ρ) fs0 c' -> realizes_cfg BDA_SEGS CFG c' T) -> realizes_cfg BDA_SEGS CFG c T.
Hypothesis Hcert : bda_cert fin = true.

Theorem bda_startup : forall (TT : list (list byte) -> TSet) (en : ExecEntry) (inp : ProcInput),
  valid_input inp ->
  valid_entry (mkImage BDA_SEGS BDA_PC BDA_PH) en inp ->
  (forall argv c, valid_argv argv -> POST argv (in_fs inp) c -> realizes_cfg BDA_SEGS CFG c (TT argv)) ->
  realizes_cfg BDA_SEGS CFG
    (init_config BDA_SEGS BDA_PC BDA_PH (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en) LIM inp)
    (TT (in_argv inp)).
Proof.
  pose proof (asum_ck_ok bda_tabs BDA_SEGS BDA_PC CFG LIM bda_img_ok bda_tabs_ok bda_cks_ok) as Hsum.
  assert (Hcfg2 : sc_alloc CFG = false) by reflexivity.
  exact (startup_sound BDA_SEGS BDA_PC BDA_PH CFG Hcfg2 LIM bda_img_ok (asum_ck bda_tabs BDA_SEGS LIM) Hsum
           POST fin Hfin_out Hbridge (mk_htable HFS) FUEL_F Hcert).
Qed.

End Startup.
