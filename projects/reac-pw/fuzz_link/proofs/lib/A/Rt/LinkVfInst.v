(* reac-pw/fuzz_link, image A (the asan build, pin 059dae63e07c): the two memory-FILE print contracts of
   LinkVfDefs.v closed at link's instance, as the walk lanes of link's own functions cite them (reac_code_emit 0x89d00
   F1 / 0x89d1c V1, reac_served_mark 0x89aec F2 / 0x89b5c F3):
   - the image's segments tfibsegs (AB1v.v), the runtime's record PcapB (AD2l.v), the FILE record link_amf
     (AMemFile.v);
   - the callers' relro bounds PCAP_RLO / PCAP_RHI (lib/A/Prog/PcapRelro.v), at which their walk invariant
     arodata_okP holds;
   - the format family FF_fmP pf_link_piece (FMsnprintfFmI.v: fmt_at, pf_parse, the pieces literal / %d / %s,
     pf_args_asan, pf_text, the format in [0x10000, 0xa2658), the slack word after each string, a nonempty format,
     each string with its NUL word in application memory), the family of link's snprintf top (LinkSnpPort.v);
   - the windows LVF_STK = 0x30 + 5552 (the vfprintf body's frame over musl vfprintf's GXA window) and LFP_STK =
     0x70 + 5552;
   - the stack-protector cells LA_GOT_GUARD 0xa2658 -> LA_GUARD 0x651c50 (LinkMfDefs.v);
   - the entries LA_W_VFPRINTF 0x4307c and LA_W_FPRINTF 0x43084, the wrappers link's code calls.
   link_ff_intro builds the family premise from its parts, pf_prec_pos discharged (link's pieces have no %.*s). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YM05 YG0f YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AD2l AMemFile.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Rt Require Import PfFacts SnShared SnFF.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require RT_pf_sh FMsnprintfFmI.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkMfDefs LinkVfDefs LinkPfPiece.
Import ListNotations.
Open Scope Z_scope.

(* the family of link's print calls *)
Definition link_vf_FF : fmt_fam := FMsnprintfFmI.FF_fmP pf_link_piece.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* vfprintf (f, fmt, ap) at the wrapper 0x4307c on link's memory FILE *)
Definition link_avfprintf_contract : Prop :=
  avfprintf_mf_realizes tfibsegs PcapB link_amf PCAP_RLO PCAP_RHI link_vf_FF LVF_STK LA_GOT_GUARD LA_GUARD
    LA_W_VFPRINTF.

(* fprintf (f, fmt, ...) at the wrapper 0x43084 on link's memory FILE *)
Definition link_afprintf_contract : Prop :=
  afprintf_mf_realizes tfibsegs PcapB link_amf PCAP_RLO PCAP_RHI link_vf_FF LFP_STK LA_GOT_GUARD LA_GUARD
    LA_W_FPRINTF.

End s.

(* link's pieces have no %.*s, so every precision fact holds *)
Lemma link_prec_pos : forall ps args, Forall pf_link_piece ps -> pf_prec_pos ps args.
Proof.
  intros ps args H. apply pf_prec_pos_nopps. eapply Forall_impl; [|exact H].
  intros p Hp E. subst p. exact Hp.
Qed.

(* the family premise from its parts *)
Lemma link_ff_intro : forall (rd : reader) (rs : list (Z * Z)) (f : Z) (fmt : list Z) (ps : list pf_piece)
    (args : list pf_arg) (ws T : list Z),
  fmt_at rd rs f fmt -> pf_parse fmt = Some ps -> Forall pf_link_piece ps ->
  pf_args_asan rd rs ws args -> pf_text ps args = Some T ->
  0x10000 <= f -> f + Z.of_nat (length fmt) + 1 <= 0xa2658 ->
  pf_args_slack ws args -> fmt <> [] -> RT_pf_sh.pf_args_amem ws args ->
  link_vf_FF rd rs f ws T.
Proof.
  intros rd rs f fmt ps args ws T Hf Hp Hk Ha Ht Hlo Hhi Hsl Hne Ham.
  exists fmt, ps, args. split; [exact Hf|]. split; [exact Hp|]. split; [exact Hk|]. split; [exact Ha|].
  split; [exact Ht|]. split; [exact (link_prec_pos ps args Hk)|].
  split; [exact Hlo|]. split; [exact Hhi|]. split; [exact Hsl|]. split; [exact Hne | exact Ham].
Qed.
