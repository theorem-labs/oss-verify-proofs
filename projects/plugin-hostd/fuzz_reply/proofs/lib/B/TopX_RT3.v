(* The image-B (fuzz_reply.asan-ubsan) twin of lib/A/TopX_RT3.v's topx_AMEMCHR / topx_AMEMMOVE, with the SAME lemma
   names: two runtime contracts AT the B top's instance ARX_rt (lib/B/TopX_RT_lock.v's verbatim copy of the B top's
   ARX, lib/B/W_LLVMFuzzerTestOneInput_top_x.v:168-169: ARcf (cp := CfParams_reply) segs TfibB /\ Hp = []), for the B
   drain walks' hypotheses (W_drain_pb.v:218-219's AMEMMOVE / AMEMCHR, W_sites_x's texts at B := TfibB, ARx := the B
   top's ARX):
     topx_AMEMCHR  : amemchr_realizesM_x segs TfibB ARX_rt 0x10350 0x10370 (SIGMA WS_memchr)
     topx_AMEMMOVE : amemmove_realizes_x TfibB ARX_rt (SIGMA WS_asan_memmove)
   Each is an existing generic proof applied at ARX_rt:
     memchr : lib/B/Rt/Memchr_x.v memchr_icpt_realizesM_x (over YE2y.icpt_laws_x + TfibSyms; its pc 0x42208 = B's
              W_place WS_memchr; its IcptRealizesX-form text at tfibsegs is W_sites_x's at pa_segs PB_fr by
              conversion, as on image A);
     memmove: lib/B/RT_asan_memmove_x.v rt_amemmove_x (over RTx.rt_laws + TfibSyms; PC_asan_memmove 0x52e5c = B's
              W_place WS_asan_memmove).
   The numerals 0x10350 / 0x10370 are image B's own: B's musl memchr (0x96950) loads its two masks from 0x10368 and
   0x10350, and YE39.v's mc_bounds computes MC_LO / MC_HI to them from B's constant table.
   icpt_laws_x at ARX_rt: RTxIcpt.icpt_laws_of_rt from TopX_RT_lock.rt_laws_ARX and the zero-shadow law of the B top's
   ARX_laws (TopX_RT_B.ARX_B_laws, that proof verbatim, stated at TopX_RT_lock.ARX_rt); TfibSyms: YD2l.TfibB_syms.
   No premise is left: every lemma here is closed. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_kit_x W_journal_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YD2l.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG0ncf YGcallcf YG0lawscf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_sites_x.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.YE2y.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.TopX_RT_lock.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.TopX_RT_B.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RTxIcpt.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Rt.Memchr_x.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_asan_memmove_x.
Import ListNotations.
Open Scope Z_scope.

Module IX := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.YE2y.
Module TRL := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.TopX_RT_lock.
Module TRB := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.TopX_RT_B.
Module RXI := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RTxIcpt.
Module MC := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Rt.Memchr_x.
Module MM := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_asan_memmove_x.

Section topx_rt3. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PB_fr).

(* the interceptor laws at ARX_rt *)
Lemma icpt_laws_ARX : IX.icpt_laws_x TfibB TRL.ARX_rt.
Proof.
  exact (RXI.icpt_laws_of_rt TfibB TRL.ARX_rt TRL.rt_laws_ARX (YCbqG.alx_zshadow _ _ _ TRB.ARX_B_laws)).
Qed.

Lemma topx_AMEMCHR : amemchr_realizesM_x segs TfibB TRL.ARX_rt 0x10350 0x10370 (SIGMA WS_memchr).
Proof. exact (MC.memchr_icpt_realizesM_x TfibB TRL.ARX_rt icpt_laws_ARX TfibB_syms). Qed.

Lemma topx_AMEMMOVE : amemmove_realizes_x TfibB TRL.ARX_rt (SIGMA WS_asan_memmove).
Proof. exact (MM.rt_amemmove_x TfibB TRL.ARX_rt TRL.rt_laws_ARX TfibB_syms). Qed.

(* ---- QMm W1 lifts (a Theorem Labs lane, 2026-10-31; a Theorem Labs lane's split 01:56Z, a Theorem Labs lane's shared lemmas in TopX_RT_lock.v):
   the two contracts above at top_x's W1 ARX, TopX_RT_lock.ARX_rtW (ARX_rt /\ arodata_ok_cf).
   - memchr writes nothing: its post keeps every view off the call's ESTACK stack window, which lies above the image
     (TRL.stk_above_img), so arodata_ok_cf carries over by TRL.aro_keep_view with X := False and Y := the window.
   - memmove writes [d, d + n) only, and its own premise puts that range off the image (W_sites_x.v:343 amemmove_realizes_x,
     `forall a, d <= a < d + n -> ~ in_img SEGS a`); a kept byte is an image byte (kept_x's first conjunct,
     Reusable/YCbqG.v:48), so the write set holds no kept byte and TRL.aentry_post_x_rtW rebuilds the post (a Theorem Labs lane
     02:13Z: no engine edit for memmove).
   The lemmas at ARX_rt stay; top_x cites the _W names. ---- *)
Lemma topx_AMEMCHR_W : amemchr_realizesM_x segs TfibB TRL.ARX_rtW 0x10350 0x10370 (SIGMA WS_memchr).
Proof.
intros ly S Hp W regs mem md x c n HPRE.
destruct (TRL.ecall_pre_rtW _ _ _ _ _ _ _ HPRE) as (HPRE0 & HQ).
pose proof HPRE0 as (HA & _ & _ & Hlo & _).
pose proof (TRL.stk_above_img _ _ _ _ _ _ HA) as HI.
intros. eapply SRr_mono; [eapply (topx_AMEMCHR ly S Hp W regs mem md x c n HPRE0); eassumption|].
intros W' c' _ (EW & regs' & mem' & md' & Hc & (HA' & HH') & Hrp & Hsm & HR & HV & Hpr).
split; [exact EW|]. exists regs', mem', md'. split; [exact Hc|].
split; [|exact (conj Hrp (conj Hsm (conj HR (conj HV Hpr))))].
split; [exact HA'|]. split; [exact HH'|].
apply (TRL.aro_keep_view ly S Hp W mem md mem' (fun _ => False) (fun a => spZ regs - ESTACK <= a < spZ regs) HA).
- intros a [].
- intros a Ha. cbv beta in Ha. unfold ESTACK in *. lia.
- intros a Ha _ HnY. exact (HV a Ha HnY).
- exact HQ.
Qed.

Lemma topx_AMEMMOVE_W : amemmove_realizes_x TfibB TRL.ARX_rtW (SIGMA WS_asan_memmove).
Proof.
intros ly S Hp W regs mem md d x n HPRE.
destruct (TRL.ecall_pre_rtW _ _ _ _ _ _ _ HPRE) as (HPRE0 & HQ).
pose proof HPRE0 as (HA & _ & _ & Hlo & _).
intros.
match goal with HIMG : forall a, d <= a < d + n -> ~ in_img _ a |- _ =>
  eapply SRr_mono; [eapply (topx_AMEMMOVE ly S Hp W regs mem md d x n HPRE0); eassumption|];
  intros W' c' _ HP;
  apply (TRL.aentry_post_x_rtW _ _ _ _ _ _ _ _ _ _ _ _ HA HQ); [| | intros a Ha HK; exact (HIMG a Ha (proj1 HK)) | exact HP]
end.
- unfold ESTACK in Hlo. lia.
- unfold ESTACK. lia.
Qed.

End topx_rt3.

Print Assumptions topx_AMEMCHR.
Print Assumptions topx_AMEMMOVE.
Print Assumptions topx_AMEMCHR_W.
Print Assumptions topx_AMEMMOVE_W.
