(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.simdjson.fuzz_utf8.images Require Import Plain.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare Frame RefMemcpyLib. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import MallocDefs ImgParams MallocSpec Img_src13 EnframeBase_src13 Enframe_src13 GetMeta_src13 FreePro_src13.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

Section Specs.
  Context {fx : FPState}.

  Lemma enframe_src13 : ENFRAME_STMT IP_src13.
  Proof.
    intros regs mem rom ret c g M W idx n h3 o16 stride start off EH R1 Hret R10 R11 R12 R13.
    replace (Z_to_bv 64 (mt_enframe (ip_M IP_src13))) with (0xb6c40%bv : word) by (apply bv_eq; reflexivity).
    destruct EH as [F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 F13 F14 F15 F16 F17 F18 F19 F20 F21 F22].
    destruct (Enframe_src13.ref_enframe regs mem rom ret c g M W idx n h3 o16 stride start off
                ltac:(constructor; assumption) R1 Hret R10 R11 R12 R13) as (regs' & mem' & RUN & K & A0 & FR & PO & FR2).
    exists regs', mem'. split; [exact RUN|]. split; [exact K|]. split; [exact A0|]. split; [exact FR|]. split; [|exact FR2].
    destruct PO as [P1 P2 P3 P4 P5 P6 P7 P8 P9]. constructor; assumption.
  Qed.

  Lemma freepro_src13 : FREEPRO_STMT IP_src13.
  Proof.
    intros regs mem rom sp p e M g idx off n stride reserved q W avail freed sec PRE H2 H10.
    replace (Z_to_bv 64 (mt_free (ip_M IP_src13))) with (0xb56a0%bv : word) by (apply bv_eq; reflexivity).
    replace (Z_to_bv 64 (mt_free_k (ip_M IP_src13))) with (0xb577c%bv : word) by (apply bv_eq; reflexivity).
    destruct PRE as [F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 F13 F14 F15 F16 F17 F18 F19 F20 F21 F22 F23 F24 F25 F26 F27 F28 F29 F30 F31 F32 F33 F34 F35 F36 F37].
    apply (FreePro_src13.ref_free_pro regs mem rom sp p e M g idx off n stride reserved q W avail freed sec); [|exact H2|exact H10].
    constructor; try assumption; cbn [mt_secret mt_sct ip_M IP_src13 MT_src13 Z.add Pos.add Pos.succ] in *; try assumption.
    (* [comment removed for export] *)
    intros i Hi. replace i with (0x21850 + (i - 0x21850)) by lia. apply fp_img. lia.
  Qed.
End Specs.
