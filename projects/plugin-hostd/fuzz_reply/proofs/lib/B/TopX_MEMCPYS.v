(* lib/B/TopX_MEMCPYS.v: image B's (fuzz_reply.asan-ubsan) __asan_memcpy onto itself, the image-B twin of a Theorem Labs lane's
   lib/A/TopX_MEMCPYS.v (a working branch b39456532c7).  RR_x's Section hypothesis
   (W_relay_remove.v:130 and the W_rr_* files)
     AMEMCPYS : amemcpy_same_realizes_x B ARx (SIGMA WS_asan_memcpy)
   PROVED at the instance of B's top_x (lib/B/W_LLVMFuzzerTestOneInput_top_x.v), B := TfibB and ARx :=
   TopX_RT_lock.ARX_rt (B top_x's ARX verbatim, as lib/B/TopX_INTRIN_memset.v uses it), so the plug is `exact` up to
   unfolding ARX.  The proof is lib/B/YE6same_x.v's acpy_same_icpt (the walk of __asan_memcpy at 0x52780 with the
   destination equal to the source, the image-B twin of lib/A/AE6same_x.v) at ARx := ARX_rt, with the interceptor law
   record lib/B/TopX_INTRIN_memset.v icpt_laws_ARX.  Changes from lib/A/TopX_MEMCPYS.v: lib.A -> lib.B modules, the
   B instance (TopX_RT_lock.ARX_rt, YD2l.TfibB_syms, TopX_INTRIN_memset.icpt_laws_ARX), and __asan_memcpy's B entry
   0x52780 (asan_memcpy_id_sigma below; A's is TopX_INTRIN.v's 0x52728).  The proof steps are A's.
   No premise is left: topx_AMEMCPYS is closed.
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_sites W_sites_x W_contract_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import TopX_RT_lock.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.TopX_INTRIN_memset.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.YE6same_x.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Module TI := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.TopX_INTRIN_memset.
Module MS := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.YE6same_x.

Section topx_memcpys. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PB_fr).

Lemma asan_memcpy_id_sigma : SIGMA WS_asan_memcpy = 0x52780.
Proof. reflexivity. Qed.

(* AMEMCPYS (W_relay_remove.v:130) at B top_x's ARX *)
Lemma topx_AMEMCPYS : amemcpy_same_realizes_x TfibB ARX_rt (SIGMA WS_asan_memcpy).
Proof.
  rewrite asan_memcpy_id_sigma.
  intros ly S Hp W regs mem md d n HPRE G10 G11 G12 Hn Hd Hdn HDST HSRC (HAM & HRA & HHULL) _ _ _.
  eapply SRr_mono.
  { exact (MS.acpy_same_icpt TfibB ARX_rt TI.icpt_laws_ARX TfibB_syms ly S Hp W regs mem md d d n HPRE G10 G11 G12
             Hn Hd Hdn HDST HAM HRA HHULL (conj Hd (conj Hdn (conj HSRC (conj eq_refl (conj HAM (conj HRA HHULL))))))). }
  intros W' c' _ (HW & regs' & mem' & md' & Hc & HAR & HPRS & HSBM & H10 & HCPY & HFR & HPRES).
  unfold aentry_post_x. split; [exact HW|]. exists regs', mem', md'.
  split; [exact Hc|]. split; [exact HAR|]. split; [exact HPRS|]. split; [exact HSBM|]. split; [exact H10|].
  split; [|exact HPRES].
  intros a Ha _ Hs.
  destruct (Z_lt_le_dec a d) as [L1|L1]; [exact (HFR a Ha ltac:(lia) Hs)|].
  destruct (Z_lt_le_dec a (d + n)) as [L2|L2]; [|exact (HFR a Ha ltac:(lia) Hs)].
  replace a with (d + (a - d)) by lia. exact (HCPY (a - d) ltac:(lia)).
Qed.

End topx_memcpys.
