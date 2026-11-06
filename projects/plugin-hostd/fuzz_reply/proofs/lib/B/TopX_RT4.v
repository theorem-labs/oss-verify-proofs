(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: row G-BRT4 (a Theorem Labs lane), the image-B (fuzz_reply.asan-ubsan) twin of lib/A/TopX_RT4.v
   (a Theorem Labs lane, commit 4d211dd95bc), with the SAME lemma names: four runtime contracts AT the B top's instance ARX_rt
   (lib/B/TopX_RT_lock.v's verbatim copy of the B top's ARX, lib/B/W_LLVMFuzzerTestOneInput_top_x.v:162-163 on this
   branch's base (154-155 at commit e43cf0c7bef): ARcf (cp := CfParams_reply) segs TfibB /\ Hp = []), for the B drain /
   send_line walks' hypotheses (W_sites_x's definitions at
   B := TfibB, ARx := the B top's ARX):
     topx_AERRNO   : aerrno_realizes_x   (PI := PB_fr) TfibB ARX_rt (SIGMA WS_errno_location)
     topx_ASTRRCHR : astrrchr_realizes_x (PI := PB_fr) TfibB ARX_rt (SIGMA WS_strrchr)
     topx_ASTRNCMP : astrncmp_realizes_x (PI := PB_fr) TfibB ARX_rt (SIGMA WS_strncmp)
     topx_ASTRCMP  : astrcmp_realizes_x  (PI := PB_fr) TfibB ARX_rt (SIGMA WS_strcmp)
   Each is the generic runtime twin (lib/B/RT___errno_location_x / RT_strrchr_x / RT_strncmp_x / RT_strcmp_x, relocated
   from lib/A by alreloc, over any ARx with RTx.rt_laws) applied at ARX_rt with TopX_RT_lock.rt_laws_ARX.  The three
   string twins also take FrShadowSyms TfibB, closed by TopX_RT_B2.fr_shadow_TfibB (TfibB's own fields: lib/B has no
   W_palib_fr, as TopX_RT_B2.v's header says), and TfibSyms TfibB by YD2l.TfibB_syms.  strrchr's cell REAL(strrchr) is
   YF0m's row 0x9fc90 (= musl strrchr 0x9740c).  No premise is left: every lemma here is closed.
   W1 lifts (a Theorem Labs lane's W1 runtime-contract lifts, decision (a)): topx_<RULE>_W states the same rule at the B top's W1
   ARX, TopX_RT_lock.ARX_rtW (ARX_rt /\ arodata_ok_cf mem). All four rules are aentry_post_x with an empty write set
   (fun _ => False), so each lift is the ARX_rt lemma above, then TopX_RT_lock.aentry_post_x_rtW: the pre's arodata at
   mem carries to the post's mem' because the post's view frame moves only the stack window, which lies above the image.
   The ARX_rt lemmas are kept unchanged. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YA0n.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_syms W_listing W_place W_tbl W_kit W_pl W_img.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YD2l.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_sites_x.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.TopX_RT_lock.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.TopX_RT_B2.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT___errno_location_x.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_strrchr_x.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_strncmp_x.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_strcmp_x.
Import ListNotations.
Open Scope Z_scope.

Module TRL := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.TopX_RT_lock.
Module TR2 := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.TopX_RT_B2.
Module ER := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT___errno_location_x.
Module SR := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_strrchr_x.
Module SN := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_strncmp_x.
Module SC := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_strcmp_x.

Section topx_rt4. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PB_fr).

Lemma topx_AERRNO : aerrno_realizes_x (PI := PB_fr) TfibB TRL.ARX_rt (SIGMA WS_errno_location).
Proof. exact (ER.rt___errno_location_x TfibB TRL.ARX_rt TRL.rt_laws_ARX). Qed.

Lemma topx_ASTRRCHR : astrrchr_realizes_x (PI := PB_fr) TfibB TRL.ARX_rt (SIGMA WS_strrchr).
Proof. exact (SR.rt_strrchr_x TfibB TRL.ARX_rt TRL.rt_laws_ARX TR2.fr_shadow_TfibB TfibB_syms). Qed.

Lemma topx_ASTRNCMP : astrncmp_realizes_x (PI := PB_fr) TfibB TRL.ARX_rt (SIGMA WS_strncmp).
Proof. exact (SN.rt_strncmp_x TfibB TRL.ARX_rt TRL.rt_laws_ARX TR2.fr_shadow_TfibB TfibB_syms). Qed.

Lemma topx_ASTRCMP : astrcmp_realizes_x (PI := PB_fr) TfibB TRL.ARX_rt (SIGMA WS_strcmp).
Proof. exact (SC.rt_strcmp_x TfibB TRL.ARX_rt TRL.rt_laws_ARX TR2.fr_shadow_TfibB TfibB_syms). Qed.

(* ---- W1 lifts: the same four rules at the B top's W1 ARX, TRL.ARX_rtW. ---- *)

Lemma topx_AERRNO_W : aerrno_realizes_x (PI := PB_fr) TfibB TRL.ARX_rtW (SIGMA WS_errno_location).
Proof.
  intros ly S Hp W regs mem md HPRE.
  destruct (TRL.ecall_pre_rtW _ _ _ _ _ _ _ HPRE) as (HPRE0 & HQ).
  eapply YA0n.SRr_mono; [exact (topx_AERRNO ly S Hp W regs mem md HPRE0)|].
  intros W' c' _ HP.
  apply (TRL.aentry_post_x_rtW _ _ _ _ _ _ _ _ _ _ _ _ (proj1 HPRE0) HQ); [| | | exact HP].
  - destruct HPRE0 as (_ & _ & _ & Hlo & _). unfold ESTACK in Hlo. lia.
  - unfold ESTACK. lia.
  - intros a Ha. destruct Ha.
Qed.

Lemma topx_ASTRRCHR_W : astrrchr_realizes_x (PI := PB_fr) TfibB TRL.ARX_rtW (SIGMA WS_strrchr).
Proof.
  intros ly S Hp W regs mem md x c k HPRE HS.
  destruct (TRL.ecall_pre_rtW _ _ _ _ _ _ _ HPRE) as (HPRE0 & HQ).
  intros.
  eapply YA0n.SRr_mono; [eapply (topx_ASTRRCHR ly S Hp W regs mem md x c k HPRE0 HS); eassumption|].
  intros W' c' _ HP.
  apply (TRL.aentry_post_x_rtW _ _ _ _ _ _ _ _ _ _ _ _ (proj1 HPRE0) HQ); [| | | exact HP].
  - destruct HS as (Hlo & _). unfold ESTACK in *. lia.
  - unfold ESTACK. lia.
  - intros a Ha. destruct Ha.
Qed.

Lemma topx_ASTRNCMP_W : astrncmp_realizes_x (PI := PB_fr) TfibB TRL.ARX_rtW (SIGMA WS_strncmp).
Proof.
  intros ly S Hp W regs mem md x y n kx ky HPRE HS.
  destruct (TRL.ecall_pre_rtW _ _ _ _ _ _ _ HPRE) as (HPRE0 & HQ).
  intros.
  eapply YA0n.SRr_mono; [eapply (topx_ASTRNCMP ly S Hp W regs mem md x y n kx ky HPRE0 HS); eassumption|].
  intros W' c' _ HP.
  apply (TRL.aentry_post_x_rtW _ _ _ _ _ _ _ _ _ _ _ _ (proj1 HPRE0) HQ); [| | | exact HP].
  - destruct HS as (Hlo & _). unfold ESTACK in *. lia.
  - unfold ESTACK. lia.
  - intros a Ha. destruct Ha.
Qed.

Lemma topx_ASTRCMP_W : astrcmp_realizes_x (PI := PB_fr) TfibB TRL.ARX_rtW (SIGMA WS_strcmp).
Proof.
  intros ly S Hp W regs mem md x y kx ky HPRE HS.
  destruct (TRL.ecall_pre_rtW _ _ _ _ _ _ _ HPRE) as (HPRE0 & HQ).
  intros.
  eapply YA0n.SRr_mono; [eapply (topx_ASTRCMP ly S Hp W regs mem md x y kx ky HPRE0 HS); eassumption|].
  intros W' c' _ HP.
  apply (TRL.aentry_post_x_rtW _ _ _ _ _ _ _ _ _ _ _ _ (proj1 HPRE0) HQ); [| | | exact HP].
  - destruct HS as (Hlo & _). unfold ESTACK in *. lia.
  - unfold ESTACK. lia.
  - intros a Ha. destruct Ha.
Qed.

End topx_rt4.

Print Assumptions topx_AERRNO.
Print Assumptions topx_ASTRRCHR.
Print Assumptions topx_ASTRNCMP.
Print Assumptions topx_ASTRCMP.
Print Assumptions topx_AERRNO_W.
Print Assumptions topx_ASTRRCHR_W.
Print Assumptions topx_ASTRNCMP_W.
Print Assumptions topx_ASTRCMP_W.
