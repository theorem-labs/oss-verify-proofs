(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk Frame.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import WpEngine LibKit StrKit WpTac WpMem.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import ACode AShadow ARt AImg ARtIc AIface.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require AIcStrlen AIcStrchr AIcStrncmp AAsanMemcpy AFakeStack.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition RTX_real (fs T ctx thr : Z) (M : mem) : Prop := ic_ok M /\ AFakeStack.fsrt_ok M fs T ctx thr.

Theorem rt_iface_real : forall fs T ctx thr, AFakeStack.fsrt_wf fs T ctx thr ->
  rt_iface (RTX_real fs T ctx thr) (AFakeStack.fsrt_dom fs T ctx thr) (fun lo n => AFakeStack.fsrt_sep lo n fs T ctx thr) fs.
Proof.
  intros fs T ctx thr Hwf. constructor.
  - intros lo n x Hs Hx. eapply AFakeStack.fsrt_sep_dom; eassumption.
  - intros lo n lo' n' Hs H1 H2. eapply AFakeStack.fsrt_sep_sub; eassumption.
  - intros M M' P [Hic Hfs] HU HP. split.
    + eapply ic_ok_unch; [exact HU | intros y Hy; apply (HP y Hy) | exact Hic].
    + eapply AFakeStack.fsrt_ok_unch; [exact Hwf | exact HU | exact HP | exact Hfs].
  - intros rom Post M h S l Hrt [Hic Hfs] Hhint Hh Hz Hfsm W1 W2 W3 W4 HS HSz Hw Hsep Hdj Hl H2 H4 K.
    eapply (AFakeStack.malloc0_cps rom Post M fs T ctx thr h S l); try eassumption.
    destruct Hfsm as ((F1 & F2) & F3). unfold FS_SIZE in *. split; [exact F1 | split; [exact F3 | exact F2]].
  - intros rom Post M d s n S l Hrt [Hic Hfs] Hn Hms Hmd Has Had Hss Hsd Hrd Hwr Hd Hdj HS HSz Hw Hdw Hl H2 H10 H11 H12 K.
    eapply (AAsanMemcpy.amemcpy_cps rom Post M d s n S l); try eassumption.
    intros l' M' Hl' Hse' _ HU' HG'. apply K; assumption.
  - intros rom Post M p N B k z S l Hrt [Hic Hfs]. intros.
    eapply (AIcStrlen.istrlen_stub_cps rom Post M p N B k z S l); eassumption.
  - intros rom Post M p N B k r c S l Hrt [Hic Hfs]. intros.
    eapply (AIcStrchr.istrchr_stub_cps rom Post M p N B k r c S l); eassumption.
  - intros rom Post M p N B k z q n RB S l Hrt [Hic Hfs]. intros.
    eapply (AIcStrncmp.istrncmp_stub_cps rom Post M p N B k z q n RB S l); eassumption.
Qed.

Print Assumptions rt_iface_real.
