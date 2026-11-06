(* fm's snprintf contract, closed: HarnessDesign's asnprintf_realizes (lib/A/FMH_Rt.v) at PC_snprintf from nothing but
   the image laws, by composing the chain's pieces:
     FMsnprintfG.v    snprintf_realizesU   the ASan interceptors, musl vsnprintf / vfprintf, the WRITE_RANGE check
     FMsnprintfPm.v   pcommon_realizesU    ASan printf_common for fm's 7 formats
     FMsnprintfPc.v   pcore_realizesU, pcore0_realizesU   musl printf_core, both passes
     FMsnprintfFw.v   afwx_realizes        musl __fwritex on the snprintf FILE (sink sn_write)
     FMsnprintfFl.v   asnflush_realizes    vfprintf's flush f->write (f, 0, 0)
     FMsnprintfMc31.v, FMsnprintfMs32.v, FMsnprintfSn.v, FMsnprintfSnN.v  the ARU memcpy / memset / strnlen
                                            interceptor contracts (the donor's, restated over Poison's ARU). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YG0d YG0f YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import
AB1v AF0m FMH_Base FMH_Rt FMsnprintfI
FMsnprintfMc31 FMsnprintfMs32 FMsnprintfSn FMsnprintfSnN
FMsnprintfFw FMsnprintfFl FMsnprintfPm FMsnprintfPc FMsnprintfG.
Local Open Scope Z_scope.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : TfibSyms B.
Lemma fm_memcpy : aintrin_realizesU B OCpy W_MEMCPY.
Proof. exact (memcpy_icpt_realizesU B LAWS TB). Qed.
Lemma fm_afwx : afwx_realizesU B A_FWX.
Proof. exact (afwx_realizes B LAWS TB fm_memcpy). Qed.
Lemma fm_asnflush : asnflush_realizesU B A_SNW.
Proof. exact (asnflush_realizes B LAWS TB fm_memcpy). Qed.
Lemma fm_pcore : apcore_realizesU B A_PCORE.
Proof.
exact (pcore_realizesU B LAWS TB fm_afwx (strnlen_icpt_realizesU B LAWS TB) (strnlen_icpt_realizesNU B LAWS TB)).
Qed.
Theorem fm_snprintf_realizes : asnprintf_realizes tfibsegs B PC_snprintf.
Proof.
exact (snprintf_realizesU B LAWS TB (pcommon_realizesU B LAWS TB) fm_pcore (pcore0_realizesU B LAWS TB)
fm_asnflush (memset_icpt_realizesU B LAWS TB)).
Qed.
End f.
