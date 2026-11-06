(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run Fs.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Ceiling RzCPS.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Sj Require Import Zpf SjTape Zpk.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec Require Import Prelim Stdio Zpb Z3o.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.AS Require Import Z10d.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.B Require Import Layout Zks Zkt Zm2 RT_rep Zl3 Zls Zm7 Zm3
  Zm4 Zm5 Zm6 Zlj Zi8 Zi9 Zl6 Zki Zis Zip Zim
  Zjl Zj1 Ziy Zju Zi7 RT_rtf RT_cli Zky D_defs Z82 Z7w
  Sj_rtf Zpo Zwn Z106 Zwc Zsl Zqf Zs4 Zqq Zqj
  Zxb Zy1 Zyo
  Z45 Z4e Z5e Z4i Z5d Z4z Z4h Z4f Z3q Z3p Z6m Z71 Z5f Z4b
  Z4x Z77 Z5y
  Z40.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Theorem rta_emplf : emplf_cpsA RTA.
Proof. exact (emplf_ok RTA rta_art_facts rta_rtf (rc2_annotate RTA rta_rc2)). Qed.
Theorem rta_empls : empls_cpsA RTA.
Proof. exact (empls_ok RTA rta_art_facts rta_rtf (rc2_annotate RTA rta_rc2)). Qed.

Theorem rta_vdes : vdestroy_cpsA RTA.
Proof. exact (vdestroy_ok RTA rta_art_facts rta_rtf (rc2_annotate RTA rta_rc2)). Qed.

Theorem rta_spl : splitinto_cpsA RTA.
Proof. exact (splitinto_closed RTA rta_art_facts rta_rtf rta_rc2). Qed.
Definition ESC : esc_okA RTA := esc_okA_closed RTA rta_art_facts rta_rc2.
Definition HELEM : forall E, aenvA_ok E -> atp_elem_cpsA RTA E TAPE_MAX_DEPTH :=
  fun E OK => atp_levelA RTA rta_art_facts rta_rc2 ESC E OK TAPE_MAX_DEPTH.

Definition client_atp : client_B :=
  mkClientB sj_lib sj_lib_loc hs_lib_ok
    (fun A nx0 LIMIT SINV argH FS0 H1 H2 H3 E ch R FULL model HC A' HA' HT => hs_lib_gen A nx0 LIMIT SINV argH FS0 H1 H2 H3 E ch R FULL model HC A' HA' HT)
    (fun RC2 => fuzz_one_closedA RTA rta_art_facts RC2
                 (fun Σ m HA => rta_got_nothrow Σ m HA) (fun Σ m HA => rta_vt_dpi Σ m HA) (fun Σ m HA => rta_vt_impl Σ m HA)
                 rta_stage2at rta_spl rta_emplf rta_empls rta_vdes HELEM).

Lemma client_atp_hs : forall h ch, HS_both h = Some ch -> cl_hs_ok client_atp ch = true.
Proof. intros h ch H. exact (HS_lib_ok h ch H). Qed.
