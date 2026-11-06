(* Three more runtime contracts AT A's top_x instance
   ARX_rt (TopX_RT.v's verbatim copy of top_x.v:125-126's ARX at integ bb9dae5d905:
   fun ly S Hp W mem md => ARcf (cp := CfParams_reply) segs TfibB ly S Hp W mem md /\ Hp = []), asked by a Theorem Labs lane
   (01:50Z) for W3's walks (a Theorem Labs lane: CSE_x / CNL_x / CSHE_x need them at ARX):
     topx_ABCMP    : abcmp_realizes_x segs TfibB ARX_rt (SIGMA WS_bcmp)                        (W_list_find.v:159's ABCMP)
     topx_AMEMCHR  : RTx.amemchr_realizesM_x segs TfibB ARX_rt 0x10350 0x10370 (SIGMA WS_memchr)
                     (= W_next_line.v:77 / W_drain_cx_x.v:162's AMEMCHR text; RTx.v:137 says verbatim, convertible)
     topx_AMEMMOVE : amemmove_realizes_x TfibB ARX_rt (SIGMA WS_asan_memmove)                   (W_drain_cx_x.v:161's AMEMMOVE)
   Each is an existing generic proof applied at ARX_rt:
     bcmp   : Rt/Bcmp.v bcmp_site_realizes_x (over AE2y.icpt_laws_x + TfibSyms);
     memchr : Rt/Memchr.v memchr_icpt_realizesM_x (over icpt_laws_x + TfibSyms; its pc 0x421b0 = W_place's WS_memchr);
     memmove: RT_asan_memmove_x.v rt_amemmove_x (over RTx.rt_laws + TfibSyms; PC_asan_memmove 0x52e04 = WS_asan_memmove).
   icpt_laws_x at ARX_rt: RTxIcpt.icpt_laws_of_rt from TopX_RT.rt_laws_ARX and the zero-shadow law of top_x.v:127-131's
   ARX_laws (TopX_RT2.ARX_rt_laws); TfibSyms: AD2l.TfibB_syms.  No premise is left: every lemma here is closed.
   QMm W1: topx_ABCMP_W / topx_AMEMCHR_W / topx_AMEMMOVE_W restate the three at top_x's W1 relation TopX_RT.ARX_rtW (the
   lift is in their comment); the ARX_rt lemmas stay for the files that cite them. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_sites_x.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.TopX_RT.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.TopX_RT2.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RTxIcpt.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Rt.RTx.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Rt.Bcmp.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Rt.Memchr.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_asan_memmove_x.
Import ListNotations.
Open Scope Z_scope.

Module T1 := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.TopX_RT.
Module T2 := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.TopX_RT2.
Module RXI := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RTxIcpt.
Module BC := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Rt.Bcmp.
Module MC := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Rt.Memchr.
Module MM := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_asan_memmove_x.

Section topx_rt3. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PB_fr).

(* the interceptor laws at ARX_rt *)
Lemma icpt_laws_ARX : AE2y.icpt_laws_x TfibB T1.ARX_rt.
Proof. exact (RXI.icpt_laws_of_rt TfibB T1.ARX_rt T1.rt_laws_ARX (YCbqG.alx_zshadow _ _ _ T2.ARX_rt_laws)). Qed.

Lemma topx_ABCMP : abcmp_realizes_x segs TfibB T1.ARX_rt (SIGMA WS_bcmp).
Proof. exact (BC.bcmp_site_realizes_x TfibB T1.ARX_rt icpt_laws_ARX TfibB_syms). Qed.

Lemma topx_AMEMCHR : RTx.amemchr_realizesM_x segs TfibB T1.ARX_rt 0x10350 0x10370 (SIGMA WS_memchr).
Proof. exact (MC.memchr_icpt_realizesM_x TfibB T1.ARX_rt icpt_laws_ARX TfibB_syms). Qed.

Lemma topx_AMEMMOVE : amemmove_realizes_x TfibB T1.ARX_rt (SIGMA WS_asan_memmove).
Proof. exact (MM.rt_amemmove_x TfibB T1.ARX_rt T1.rt_laws_ARX TfibB_syms). Qed.

(* QMm W1 (a Theorem Labs lane 01:57Z split, lead a Theorem Labs lane): the three rows at top_x's W1 relation TopX_RT.ARX_rtW (top_x's ARX
   verbatim, carrying arodata_ok_cf).  Each splits the W1 pre (TopX_RT.ecall_pre_rtW), runs the ARX_rt row above, and
   rebuilds the post.  bcmp and memchr change nothing outside their stack window ([sp - 2 ESTACK, sp) and
   [sp - ESTACK, sp)), which lies above the image (TopX_RT.stk_above_img), so arodata_ok_cf survives by
   TopX_RT.aro_keep_view with the write set False.  memmove's post is aentry_post_x with the write set [d, d + n); its
   contract already puts that range off the image (amemmove_realizes_x's last premise), so it holds no kept byte
   (YCbqG.kept_x_off_img: a kept byte is in the image) and TopX_RT.aentry_post_x_rtW applies; no engine edit is needed. *)
Lemma topx_ABCMP_W : abcmp_realizes_x segs TfibB T1.ARX_rtW (SIGMA WS_bcmp).
Proof.
  intros ly S Hp W regs mem md x y n HPRE Hlo Hpres G10 G11 G12 Hn Hx Hxn Hy Hyn HSX HSY HNX HNY HAX HAY HRX HHX HRY HHY.
  destruct (T1.ecall_pre_rtW _ _ _ _ _ _ _ HPRE) as (HPRE0 & HQ).
  eapply SRr_mono;
    [exact (topx_ABCMP ly S Hp W regs mem md x y n HPRE0 Hlo Hpres G10 G11 G12 Hn Hx Hxn Hy Hyn HSX HSY HNX HNY HAX HAY
              HRX HHX HRY HHY)|].
  intros W' c' _ (EW & regs' & mem' & md' & v & Hc & (HA' & HH') & Hrp & Hsm & H10 & Hv & HV & Hpr).
  split; [exact EW|]. exists regs', mem', md', v. split; [exact Hc|]. split.
  - split; [exact HA'|]. split; [exact HH'|].
    pose proof (T1.stk_above_img _ _ _ _ _ _ (proj1 HPRE0)) as HI.
    apply (T1.aro_keep_view ly S Hp W mem md mem' (fun _ => False) (fun a => spZ regs - 2 * ESTACK <= a < spZ regs)
             (proj1 HPRE0)); [intros a [] | | | exact HQ].
    + intros a Ha. cbv beta in Ha. unfold ESTACK in *. lia.
    + intros a Hb _ Hw. exact (HV a Hb Hw).
  - exact (conj Hrp (conj Hsm (conj H10 (conj Hv (conj HV Hpr))))).
Qed.

Lemma topx_AMEMCHR_W : RTx.amemchr_realizesM_x segs TfibB T1.ARX_rtW 0x10350 0x10370 (SIGMA WS_memchr).
Proof.
  intros ly S Hp W regs mem md x c n HPRE G10 G11 G12 Hc Hn Hx Hxn HSRC HAM HRA HHULL HCV.
  destruct (T1.ecall_pre_rtW _ _ _ _ _ _ _ HPRE) as (HPRE0 & HQ).
  eapply SRr_mono;
    [exact (topx_AMEMCHR ly S Hp W regs mem md x c n HPRE0 G10 G11 G12 Hc Hn Hx Hxn HSRC HAM HRA HHULL HCV)|].
  intros W' c' _ (EW & regs' & mem' & md' & Hc' & (HA' & HH') & Hrp & Hsm & HK & HV & Hpr).
  split; [exact EW|]. exists regs', mem', md'. split; [exact Hc'|]. split.
  - split; [exact HA'|]. split; [exact HH'|].
    pose proof (T1.stk_above_img _ _ _ _ _ _ (proj1 HPRE0)) as HI.
    pose proof HPRE0 as (_ & _ & _ & Hlo & _).
    apply (T1.aro_keep_view ly S Hp W mem md mem' (fun _ => False) (fun a => spZ regs - ESTACK <= a < spZ regs)
             (proj1 HPRE0)); [intros a [] | | | exact HQ].
    + intros a Ha. cbv beta in Ha. unfold ESTACK in *. lia.
    + intros a Hb _ Hw. exact (HV a Hb Hw).
  - exact (conj Hrp (conj Hsm (conj HK (conj HV Hpr)))).
Qed.

Lemma topx_AMEMMOVE_W : amemmove_realizes_x TfibB T1.ARX_rtW (SIGMA WS_asan_memmove).
Proof.
  intros ly S Hp W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST HAM HRA HHULL Hx Hxn HSRC HAMx HRAx HHULLx HROM H8 HNI.
  destruct (T1.ecall_pre_rtW _ _ _ _ _ _ _ HPRE) as (HPRE0 & HQ).
  eapply SRr_mono;
    [exact (topx_AMEMMOVE ly S Hp W regs mem md d x n HPRE0 G10 G11 G12 Hn Hd Hdn HDST HAM HRA HHULL Hx Hxn HSRC HAMx HRAx
              HHULLx HROM H8 HNI)|].
  intros W' c' _ HP.
  apply (T1.aentry_post_x_rtW _ _ _ _ _ _ _ _ _ _ _ _ (proj1 HPRE0) HQ); [| | | exact HP].
  - destruct HPRE0 as (_ & _ & _ & Hlo & _). unfold ESTACK in Hlo. lia.
  - unfold ESTACK. lia.
  - intros a Ha HK. exact (HNI a Ha (proj1 HK)).
Qed.

End topx_rt3.
