(* lib/B/TopX_INTRIN_memcpy.v: image B's (fuzz_reply.asan-ubsan) memcpy row of top_x group INTRIN, the image-B twin of the
   memcpy row of a Theorem Labs lane's lib/A/TopX_INTRIN.v (sha256 bf3d08d5e5bf; internal record, last changed at 3333ca009fab; its memset row's B twin
   is lib/B/TopX_INTRIN_memset.v).  The intrinsic contract of __asan_memcpy (B entry 0x52780) PROVED at image B's top_x
   instance
     AMEMCPY_x : aintrin_realizes_x segs TfibB ARX OCpy (pa_sigma WS_asan_memcpy)
   with ARX := TopX_RT_lock.ARX_rt (lib/B/W_LLVMFuzzerTestOneInput_top_x.v's ARX verbatim), so the plug is `exact` up to
   unfolding ARX.  The proof is the ARx port of the __asan_memcpy walk at ARx := ARX_rt: lib/B/YE6k_x.v .. YE6s_x.v,
   YE2q_x.v asan_memcpy_realizes_x over YE2y.icpt_laws_x (the image-B twins of lib/A/AE6k_x.v .. AE6s_x.v, AE2q_x.v), with
   the interceptor law record lib/B/TopX_INTRIN_memset.v icpt_laws_ARX and __asan_memcpy's B entry
   lib/B/TopX_MEMCPYS.v asan_memcpy_id_sigma.  The proof steps are A's.  No premise is left.
   W1 (a Theorem Labs lane, 2026-10-31, a Theorem Labs lane's ask): the W1 engine gave aintrin_realizes_x the premise
   `(forall a, d <= a < d + n -> ~ kept_x segs B a)` after `amem_range d n`; YE2q_x's walk does not read it, so
   topx_AMEMCPY_x takes it and drops it (the pattern of lib/B/YE2t.v ocpy_of_icpt).  topx_AMEMCPY_W states the same
   rule at the W1 relation TopX_RT_lock.ARX_rtW: topx_AMEMCPY_x's post, with the arodata fact carried by
   TopX_RT_lock.aro_keep_view (X := the destination, not kept by the rule's own premise; Y := the ESTACK window below
   sp, above the image by stk_above_img).
   rule 24: no function proved. rule 24: proves no function (kind: statement text). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_sites_x W_contract_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import TopX_RT_lock.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.TopX_INTRIN_memset.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.TopX_MEMCPYS.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.YE2q_x.
Import ListNotations.
Open Scope Z_scope.

Module TI := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.TopX_INTRIN_memset.
Module MS := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.TopX_MEMCPYS.
Module CPY := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.YE2q_x.

Section topx_intrin_memcpy. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PB_fr).

(* AMEMCPY_x (the hypothesis image B's top_x takes at ARX) *)
Lemma topx_AMEMCPY_x : aintrin_realizes_x segs TfibB ARX_rt OCpy (SIGMA WS_asan_memcpy).
Proof.
  rewrite MS.asan_memcpy_id_sigma.
  intros ly S Hp W regs mem md d x n P1 P2 P3 P4 P5 P6 P7 P8 P9 _.
  exact (CPY.asan_memcpy_realizes_x TfibB ARX_rt TI.icpt_laws_ARX TfibB_syms ly S Hp W regs mem md d x n
    P1 P2 P3 P4 P5 P6 P7 P8 P9).
Qed.

(* AMEMCPY at the W1 relation ARX_rtW: the same post, the arodata fact carried to the post's memory *)
Lemma topx_AMEMCPY_W : aintrin_realizes_x segs TfibB ARX_rtW OCpy (SIGMA WS_asan_memcpy).
Proof.
  intros ly S Hp W regs mem md d x n HPRE H10 H11 H12 Hn Hd Hdn HDEST HAMR HNK HRA HSH HOP.
  destruct (ecall_pre_rtW _ _ _ _ _ _ _ HPRE) as (HPRE0 & HQ).
  eapply SRr_mono;
    [exact (topx_AMEMCPY_x ly S Hp W regs mem md d x n HPRE0 H10 H11 H12 Hn Hd Hdn HDEST HAMR HNK HRA HSH HOP)|].
  intros W' c' _ (-> & regs' & mem' & md' & Hc & (HA' & HH') & Hrp & Hsm & H10' & Hcp & Hfr & Hpr).
  split; [reflexivity|]. exists regs', mem', md'.
  split; [exact Hc|]. split; [|exact (conj Hrp (conj Hsm (conj H10' (conj Hcp (conj Hfr Hpr)))))].
  refine (conj HA' (conj HH' _)).
  apply (aro_keep_view ly S Hp W mem md mem' (fun a => d <= a < d + n) (fun a => spZ regs - ESTACK <= a < spZ regs)
    (proj1 HPRE0) HNK); [| exact Hfr | exact HQ].
  intros a Ha. pose proof (stk_above_img _ _ _ _ _ _ (proj1 HPRE0)) as HS.
  destruct HPRE0 as (_ & _ & _ & Hlo & _). unfold ESTACK in *. lia.
Qed.

End topx_intrin_memcpy.

Print Assumptions topx_AMEMCPY_x.
Print Assumptions topx_AMEMCPY_W.
