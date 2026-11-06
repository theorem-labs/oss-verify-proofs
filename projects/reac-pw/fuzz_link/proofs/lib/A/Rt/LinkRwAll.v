(* reac-pw/fuzz_link, image A (pin 059dae63e07c): the rewind path at link's own instance, with no hypothesis left.

   Each walk of this group is proved for every B with PcapSyms B and takes its callees' contracts as Section
   hypotheses (lib/A/Rt/LinkRwMseek.v, LinkRwMwrite0.v, LinkRwMwrite.v, LinkRwFseeko.v, LinkRwRewind.v). This file
   closes them at B = PcapB (lib/A/AD2l.v, with PcapB_syms) and composes them bottom-up:
     mseek (no hypothesis)
     mwrite at k = 0                       <- the runtime's memcpy interceptor 0x52d74 (the frame's lib/A/AE31.v
                                              memcpy_icpt_realizes, under AR_laws, which lib/Reusable/YG0q.v proves)
     mwrite in general, and its flush      <- the memcpy interceptor and mwrite at k = 0 (the inner self-call)
     __fseeko_unlocked (off 0, SEEK_SET)   <- the flush and mseek (its two indirect calls through f->write, f->seek)
     musl rewind, ___interceptor_rewind,
     its trampoline                        <- __fseeko_unlocked
   `link_arewind_ok` is the contract mark_quietly's walk cites at 0x88424 (`jal 0x430d4`, a0 = g_sink).
   Proves no function itself (kind: assembly). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YM05 YG00 YG0f YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AF0l AF0m AD2l AMemFile.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AE31.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkMfDefs LinkRwDefs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import
  LinkRwMseek LinkRwMwrite0 LinkRwMwrite LinkRwFseeko LinkRwRewind.
Local Open Scope Z_scope.

Section I. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* the memcpy interceptor mwrite calls at +0xc0 (pc_wrap_memcpy Tfib_code = 0x52d74) *)
Lemma link_amemcpy_icpt : aintrin_realizes tfibsegs PcapB OCpy (pc_wrap_memcpy (as_code PcapB)).
Proof.
  rewrite (ts_code PcapB PcapB_syms).
  exact (AE31.memcpy_icpt_realizes PcapB (YG0q.AR_laws_ok tfibsegs PcapB) PcapB_syms).
Qed.

(* Each walk theorem takes, after B, only the Section hypotheses its proof used (Coq drops an unused one, as
   LinkRwMseek.v drops PcapSyms B), so the closing steps apply the theorem and discharge whatever it asks. *)
Ltac rw_close := first [ exact PcapB_syms | exact link_amemcpy_icpt | assumption ].

Theorem link_amseek_ok : amseek_set_realizes tfibsegs PcapB link_amf LA_MSEEK.
Proof. apply link_amseek_set; rw_close. Qed.

Theorem link_amwrite_k0_ok : amwrite_mf_k0_realizes tfibsegs PcapB link_amf LA_MWRITE.
Proof. apply link_amwrite_k0; rw_close. Qed.

Theorem amwrite_mf_ok : amwrite_mf_realizes tfibsegs PcapB link_amf LA_MWRITE.
Proof. pose proof link_amwrite_k0_ok. apply link_amwrite_gen; rw_close. Qed.

Theorem amwrite_mf_flush_ok : amwrite_mf_flush_realizes tfibsegs PcapB link_amf LA_MWRITE.
Proof. pose proof link_amwrite_k0_ok. apply link_amwrite_flush; rw_close. Qed.

Theorem link_afseeko0_ok : afseeko0_mf_realizes tfibsegs PcapB link_amf LA_FSEEKO.
Proof. pose proof amwrite_mf_flush_ok. pose proof link_amseek_ok. apply link_afseeko0; rw_close. Qed.

Theorem link_arewind_musl_ok : arewind_mf_realizes tfibsegs PcapB link_amf LA_REWIND.
Proof. pose proof link_afseeko0_ok. apply link_arewind_musl; rw_close. Qed.

Theorem link_arewind_icpt_ok : arewind_mf_realizes tfibsegs PcapB link_amf LA_I_REWIND.
Proof. pose proof link_afseeko0_ok. apply link_arewind_icpt; rw_close. Qed.

(* the contract at the wrapper's trampoline, which mark_quietly's walk cites *)
Theorem link_arewind_ok : arewind_mf_realizes tfibsegs PcapB link_amf LA_W_REWIND.
Proof. pose proof link_afseeko0_ok. apply link_arewind_mf_ok; rw_close. Qed.

End I.

About link_arewind_ok.
Print Assumptions link_arewind_ok.
About amwrite_mf_ok.
Print Assumptions amwrite_mf_ok.
About amwrite_mf_flush_ok.
Print Assumptions amwrite_mf_flush_ok.
Print Assumptions link_afseeko0_ok.
Print Assumptions link_amseek_ok.
Print Assumptions link_arewind_musl_ok.
Print Assumptions link_arewind_icpt_ok.
