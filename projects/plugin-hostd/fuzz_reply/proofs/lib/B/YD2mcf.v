(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: image B's twin of lib/A/AD2mcf.v (a working branch 46f1762ad5a), in place of A1's raw
   generator copy of lib/B/YD2m.v (88ba9e5b87c). It is the cf twin of B/YD2m.v - the two interceptor results the
   fuzz_reply driver calls, over the event-free second allocator instance ARcf (Reusable/YG0ncf.v) instead of cgif's AR:
     tfib_AICPY_cf  : aintrin_realizes_cf tfibsegs B OCpy (pc_wrap_memcpy (as_code B))   (B/YD2m.v:17 tfib_AICPY)
     tfib_ARDCHK_cf : YD1icf.aread_check_stmt B                                           (B/YD2m.v:22 tfib_ARDCHK)
   Both come from the SAME walks as the AR versions: B/YE31.v memcpy_icpt_realizes_x and B/YE33.v
   aread_check_realizes_x are those walks stated over an arbitrary allocator invariant ARx (B/YE2y.v's
   icpt_laws_x / ecall_pre_ix; row A4's conversion acd4eb7f7c6), and YE31.memcpy_icpt_realizes /
   YE33.aread_check_realizes are their cgif AR instances, with their statement text unchanged. icpt_laws_x_cf below is
   the ARcf instance of the law record: every field is a field of AR_laws_cf (YG0dcf.v) or of ARmcf (YG0ncf.v), so the
   record is discharged by citation, with no new allocator fact.
   The only image facts are B's own: TfibSyms / ts_code (B/YF0m.v) and the B walks (B/YE31.v, B/YE33.v).
   No address and no image numeral appears here. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0f YG00 YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YF0m YD20 YE2y YE31 YE33.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0d2cf YG0dcf YG0ncf YG0lawscf YGcfNames.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YD1icf.
Unset Lia Cache. Unset Nia Cache.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Context {ci : YGcfNames.CfImg} {cp : YGcfNames.CfParams}.
(* The walks' law record at ARcf: alc_frame / alc_stack / alc_zshadow are AR_laws_cf's own fields (YG0dcf.v),
   with the same binder order; the const cells and layout_ok are ARmcf's amc_const / amc_layout (YG0ncf.v). *)
Lemma icpt_laws_x_cf : forall B, AR_laws_cf tfibsegs B ->
icpt_laws_x B (fun ly S Hp W mem md => ARcf tfibsegs B ly S Hp W mem md).
Proof.
intros B L. constructor.
- exact (alc_frame _ _ L).
- exact (alc_stack _ _ L).
- exact (alc_zshadow _ _ L).
- intros ly S Hp W mem md (M & _). exact (amc_const _ _ _ _ _ M).
- intros ly S Hp W mem md (M & _). exact (amc_layout _ _ _ _ _ M).
Qed.
Variable B : asyms.
Hypothesis HB : TfibSyms B.
Lemma tfib_AICPY_cf : aintrin_realizes_cf tfibsegs B OCpy (pc_wrap_memcpy (as_code B)).
Proof.
pose proof (memcpy_icpt_realizes_x B (fun ly S Hp W mem md => ARcf tfibsegs B ly S Hp W mem md)
(icpt_laws_x_cf B (AR_laws_ok_cf tfibsegs B)) HB) as H.
unfold aintrin_realizes_cf. rewrite (ts_code B HB). exact H.
Qed.
Lemma tfib_ARDCHK_cf : YD1icf.aread_check_stmt B.
Proof.
exact (aread_check_realizes_x B (fun ly S Hp W mem md => ARcf tfibsegs B ly S Hp W mem md)
(icpt_laws_x_cf B (AR_laws_ok_cf tfibsegs B)) HB).
Qed.
End a.
