(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec StoreOk ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIfaceABx StrictOfB.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section StrictI.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (scfg : SpuriousCfg) (HIR : asan_iface).
Hypothesis IMG : hl_img_hi L <= BIGSHADOW_LO.
Hypothesis OK : HAJ.asan_iface_okR L ar C scfg HIR.
Hypothesis ICPT : aicpt_ok L ar IL scfg HIR.
#[local] Abbreviation HIS := (HAJ.strict_of HIR).

#[using="OK ICPT"] Theorem strict_strlen : astrlen_spec L ar IL scfg HIS.
Proof.
  intros fx R M model LB FF LK cr A s K buf Kt sp (RI & SB & FC) HALT MI H10 Htp Hra STK Hs Hsb HK RD Hal HNUL HNZ CLS RO AC APR K0 POST.
  pose proof (sj_wf_of L ar C scfg HIR OK LB FF LK cr A M (vml_of model) RI) as WF.
  apply (aic_strlen _ _ _ _ _ ICPT fx R M model LB FF LK cr A s K buf Kt RI HALT MI H10 Htp Hra STK Hs Hsb HK RD Hal HNUL HNZ CLS RO AC APR K0).
  intros R' M' model' H10' RP KEEP SCR DEF MRT MI' RI'.
  apply (POST R' M' model' H10' RP KEEP SCR DEF MRT MI'). split; [exact RI'|]. split; [|exact FC].
  exact (sj_keep_pres L ar LB LB FF LK sp (icl_scr_strlen IL) M M' WF (incl_refl _) (conj KEEP SCR) SB).
Qed.

#[using="IMG OK ICPT"] Theorem strict_icpt : aicpt_ok L ar IL scfg HIS.
Proof.
  constructor.
  - exact strict_strlen.
  - intros LB FF LK cr A M V (RI & _ & _). exact (aic_globals _ _ _ _ _ ICPT LB FF LK cr A M V RI).
  - intros LB FF LK cr A M V (RI & _ & _). exact (aic_img_shadow _ _ _ _ _ ICPT LB FF LK cr A M V RI).
  - intros LB FF LK cr A M V (RI & _ & _). exact (aic_shadow_defined _ _ _ _ _ ICPT LB FF LK cr A M V RI).
  - intros LB FF LK cr A M model (RI & _ & _). exact (aic_tls _ _ _ _ _ ICPT LB FF LK cr A M model RI).
  - exact (strict_memcpy_at L ar C scfg HIR IMG OK _ _ (aic_memcpy_libc _ _ _ _ _ ICPT)).
  - exact (strict_memcpy_at L ar C scfg HIR IMG OK _ _ (aic_memmove_libc _ _ _ _ _ ICPT)).
Qed.
End StrictI.
