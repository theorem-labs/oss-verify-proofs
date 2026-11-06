(* Four more runtime contracts AT A's top_x instance
   ARX_rt (TopX_RT.v's verbatim copy of top_x's ARX: ARcf (cp := CfParams_reply) segs TfibB /\ Hp = []), asked by
   a Theorem Labs lane (08:39Z) for a Theorem Labs lane's DR_x drain walk (pb_drain_x states each as `<x>_realizes_x B ARx (SIGMA WS_<x>)`,
   W_sites_x's definitions, plugged at B := TfibB, ARx := top_x's ARX):
     topx_AERRNO   : aerrno_realizes_x   (PI := PB_fr) TfibB ARX_rt (SIGMA WS_errno_location)
     topx_ASTRRCHR : astrrchr_realizes_x (PI := PB_fr) TfibB ARX_rt (SIGMA WS_strrchr)
     topx_ASTRNCMP : astrncmp_realizes_x (PI := PB_fr) TfibB ARX_rt (SIGMA WS_strncmp)
     topx_ASTRCMP  : astrcmp_realizes_x  (PI := PB_fr) TfibB ARX_rt (SIGMA WS_strcmp)
   Each is the generic runtime twin (RT___errno_location_x / RT_strrchr_x / RT_strncmp_x / RT_strcmp_x, over any ARx with
   RTx.rt_laws) applied at ARX_rt with TopX_RT.rt_laws_ARX.  The three string twins also take FrShadowSyms (discharged by
   RT_kit.fr_shadow_of_palib on W_palib_fr.palib_tfib TfibB TfibB_syms) and TfibSyms (AD2l.TfibB_syms); strrchr's cell
   REAL(strrchr) is AF0m's row 0x9f710 (index 405).  No premise is left: every lemma here is closed.
   QMm W1 (a Theorem Labs lane, 2026-10-31; owner a Theorem Labs lane 01:53Z, shape a Theorem Labs lane 02:13Z, the image-B worked rule of
   a Theorem Labs lane): the same four rows AT top_x's W1 relation TopX_RT.ARX_rtW (top_x's ARX with arodata_ok_cf as its
   last conjunct), added as topx_<RULE>_W; the rows above stay and are what each _W row runs. Each _W row takes the
   ARX_rt pre and the pre-state's arodata from TopX_RT.ecall_pre_rtW, runs the row above under SRr_mono, and closes
   with TopX_RT.aentry_post_x_rtW: all four posts are aentry_post_x with write set False, so arodata at the post
   follows from the post's view frame (only the stack window [sp - stk, sp), stk = ESTACK or 2 * ESTACK, may move,
   and it lies above the image). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_kit_x W_journal_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AD2l CfImgA CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG0ncf YGcallcf YG0lawscf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_sites_x W_palib_fr.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.TopX_RT.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_kit.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT___errno_location_x.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_strrchr_x.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_strncmp_x.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_strcmp_x.
Import ListNotations.
Open Scope Z_scope.

Module T1 := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.TopX_RT.
Module K := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_kit.
Module ER := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT___errno_location_x.
Module SR := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_strrchr_x.
Module SN := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_strncmp_x.
Module SC := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_strcmp_x.

Section topx_rt4. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PB_fr).

Lemma topx_AERRNO : aerrno_realizes_x (PI := PB_fr) TfibB T1.ARX_rt (SIGMA WS_errno_location).
Proof. exact (ER.rt___errno_location_x TfibB T1.ARX_rt T1.rt_laws_ARX). Qed.

Lemma topx_ASTRRCHR : astrrchr_realizes_x (PI := PB_fr) TfibB T1.ARX_rt (SIGMA WS_strrchr).
Proof.
  exact (SR.rt_strrchr_x TfibB T1.ARX_rt T1.rt_laws_ARX
           (K.fr_shadow_of_palib TfibB (palib_tfib TfibB TfibB_syms)) TfibB_syms).
Qed.

Lemma topx_ASTRNCMP : astrncmp_realizes_x (PI := PB_fr) TfibB T1.ARX_rt (SIGMA WS_strncmp).
Proof.
  exact (SN.rt_strncmp_x TfibB T1.ARX_rt T1.rt_laws_ARX
           (K.fr_shadow_of_palib TfibB (palib_tfib TfibB TfibB_syms)) TfibB_syms).
Qed.

Lemma topx_ASTRCMP : astrcmp_realizes_x (PI := PB_fr) TfibB T1.ARX_rt (SIGMA WS_strcmp).
Proof.
  exact (SC.rt_strcmp_x TfibB T1.ARX_rt T1.rt_laws_ARX
           (K.fr_shadow_of_palib TfibB (palib_tfib TfibB TfibB_syms)) TfibB_syms).
Qed.

(* ---- QMm W1: the four rows at TopX_RT.ARX_rtW (no-write lifts; write set False) ---- *)
Lemma topx_AERRNO_W : aerrno_realizes_x (PI := PB_fr) TfibB T1.ARX_rtW (SIGMA WS_errno_location).
Proof.
intros ly S Hp W regs mem md HPRE.
destruct (T1.ecall_pre_rtW _ _ _ _ _ _ _ HPRE) as (HPRE0 & HQ).
eapply SRr_mono; [exact (topx_AERRNO ly S Hp W regs mem md HPRE0)|].
intros W' c' _ HP.
apply (T1.aentry_post_x_rtW _ _ _ _ _ _ _ _ _ _ _ _ (proj1 HPRE0) HQ); [| | | exact HP].
- destruct HPRE0 as (_ & _ & _ & Hlo & _). unfold ESTACK in Hlo. lia.
- unfold ESTACK. lia.
- intros a Ha. destruct Ha.
Qed.

Lemma topx_ASTRRCHR_W : astrrchr_realizes_x (PI := PB_fr) TfibB T1.ARX_rtW (SIGMA WS_strrchr).
Proof.
intros ly S Hp W regs mem md x c k HPRE.
destruct (T1.ecall_pre_rtW _ _ _ _ _ _ _ HPRE) as (HPRE0 & HQ).
intros. eapply SRr_mono; [eapply (topx_ASTRRCHR ly S Hp W regs mem md x c k HPRE0); eassumption|].
intros W' c' _ HP.
apply (T1.aentry_post_x_rtW _ _ _ _ _ _ _ _ _ _ _ _ (proj1 HPRE0) HQ); [| | | exact HP].
- destruct HPRE0 as (_ & _ & _ & Hlo & _). unfold ESTACK in Hlo. lia.
- unfold ESTACK. lia.
- intros a Ha. destruct Ha.
Qed.

Lemma topx_ASTRNCMP_W : astrncmp_realizes_x (PI := PB_fr) TfibB T1.ARX_rtW (SIGMA WS_strncmp).
Proof.
intros ly S Hp W regs mem md x y n kx ky HPRE.
destruct (T1.ecall_pre_rtW _ _ _ _ _ _ _ HPRE) as (HPRE0 & HQ).
intros. eapply SRr_mono; [eapply (topx_ASTRNCMP ly S Hp W regs mem md x y n kx ky HPRE0); eassumption|].
intros W' c' _ HP.
apply (T1.aentry_post_x_rtW _ _ _ _ _ _ _ _ _ _ _ _ (proj1 HPRE0) HQ); [| | | exact HP].
- destruct HPRE0 as (_ & _ & _ & Hlo & _). unfold ESTACK in Hlo. lia.
- unfold ESTACK. lia.
- intros a Ha. destruct Ha.
Qed.

Lemma topx_ASTRCMP_W : astrcmp_realizes_x (PI := PB_fr) TfibB T1.ARX_rtW (SIGMA WS_strcmp).
Proof.
intros ly S Hp W regs mem md x y kx ky HPRE.
destruct (T1.ecall_pre_rtW _ _ _ _ _ _ _ HPRE) as (HPRE0 & HQ).
intros. eapply SRr_mono; [eapply (topx_ASTRCMP ly S Hp W regs mem md x y kx ky HPRE0); eassumption|].
intros W' c' _ HP.
apply (T1.aentry_post_x_rtW _ _ _ _ _ _ _ _ _ _ _ _ (proj1 HPRE0) HQ); [| | | exact HP].
- destruct HPRE0 as (_ & _ & _ & Hlo & _). unfold ESTACK in Hlo. lia.
- unfold ESTACK. lia.
- intros a Ha. destruct Ha.
Qed.

End topx_rt4.
