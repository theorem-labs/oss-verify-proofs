(* Modified by Theorem Labs, 2026-10: the image-B CSE row's runtime piece at the B top's W1 ARX (QMm W1, a Theorem Labs lane's
   B W1 rows, 2026-10-31). lib/B/W_LLVMFuzzerTestOneInput_top_x.v's Section hypothesis
     Hypothesis CSE_x : cse_spec_x (PI := PB_fr) TfibB [] ARX (BASE + AF_fr_check_shape_event).
   is built, as on image A (lib/A/W_LLVMFuzzerTestOneInput_top_x.v:1531), by W_check_shape_event.pb_check_shape_event_x at
   top_x's ARX, whose bcmp premise is ABCMP : abcmp_realizes_x SEGS B ARx (SIGMA WS_bcmp). Image B proves bcmp only at
   ARX_B (TopX_RT_B.topx_ABCMP_B, ARcf /\ Hp = []); top_x's ARX is TopX_RT_lock.ARX_rtW (the same plus arodata_ok_cf).
     topx_ABCMP_W : abcmp_realizes_x segs TfibB TRL.ARX_rtW (SIGMA WS_bcmp)
   is that lift, the TopX_RT3 topx_AMEMCHR_W way: bcmp writes nothing and its post keeps every view off its stack window
   [spZ regs - 2 * ESTACK, spZ regs), which lies above the image (TopX_RT_lock.stk_above_img), so arodata_ok_cf survives
   (TopX_RT_lock.aro_keep_view with an empty write set). *)
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
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.TopX_RT_lock.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.TopX_RT_B.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.TopX_RT_B2.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.TopX_RT3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import CfImgB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YG0dcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyKeptAroB W_palib.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_contract_x W_next_line W_check_shape_done
  W_check_shape_event.
Import ListNotations.
Open Scope Z_scope.

Module TRL := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.TopX_RT_lock.
Module TRB := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.TopX_RT_B.
Module TR2 := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.TopX_RT_B2.
Module TR3 := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.TopX_RT3.

Section topx_cse. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PB_fr).

Lemma topx_ABCMP_W : abcmp_realizes_x segs TfibB TRL.ARX_rtW (SIGMA WS_bcmp).
Proof.
intros ly S Hp W regs mem md x y n HPRE Hlo Hsc.
destruct (TRL.ecall_pre_rtW _ _ _ _ _ _ _ HPRE) as (HPRE0 & HQ).
pose proof (TRL.stk_above_img _ _ _ _ _ _ (proj1 HPRE0)) as HI.
intros. eapply SRr_mono; [eapply (TRB.topx_ABCMP_B ly S Hp W regs mem md x y n HPRE0 Hlo Hsc); eassumption|].
intros W' c' _ (EW & regs' & mem' & md' & v & Hc & (HA' & HH') & Hrp & Hsm & Hv & Heq & HV & Hpr).
split; [exact EW|]. exists regs', mem', md', v. split; [exact Hc|].
split; [|exact (conj Hrp (conj Hsm (conj Hv (conj Heq (conj HV Hpr)))))].
split; [exact HA'|]. split; [exact HH'|].
apply (TRL.aro_keep_view ly S Hp W mem md mem' (fun _ => False) (fun a => spZ regs - 2 * ESTACK <= a < spZ regs)
  (proj1 HPRE0)).
- intros a [].
- intros a Ha. cbv beta in Ha. unfold ESTACK in *. lia.
- intros a Ha _ HnY. exact (HV a Ha HnY).
- exact HQ.
Qed.

End topx_cse.

(* ---- the CSE row, closed: check_shape_event's walk at top_x's ARX (TRL.ARX_rtW), as image A's top_x.v:1452 builds it.
   Its premises at ARX_rtW: the laws (lib/B/W_LLVMFuzzerTestOneInput_top_x.v ARX_laws, that proof verbatim at ARX_rtW, the same body), HP0, strlen
   (TopX_RT_B2.topx_ASTRLEN_B_W), bcmp (topx_ABCMP_W above), next_line (W_next_line.pb_next_line_x over ARx, from
   a Theorem Labs lane's working branch 712a17060d24, with memchr TopX_RT3.topx_AMEMCHR_W), check_shape_done
   (W_check_shape_done.pb_check_shape_done_x) and PALib TfibB (W_palib.pb_palib_tfib, as ReplyBTop closes TL). ---- *)
Section topx_cse_w. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Local Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
Lemma ARX_rtW_laws : AR_laws_x segs TfibB TRL.ARX_rtW (@cf_head CfParams_reply).
Proof.
  apply (AR_laws_x_iff segs TfibB (fun ly S Hp W mem md =>
           (ARcf (ci := CfImg_B) (cp := CfParams_reply) segs TfibB ly S Hp W mem md /\ Hp = []) /\
           @YG0dcf.arodata_ok_cf CfImg_B segs TfibB mem)).
  { intros ly S Hp W mem md. unfold TRL.ARX_rtW. split.
    - intros ((H1 & H2) & H3). exact (conj H1 (conj H2 H3)).
    - intros (H1 & H2 & H3). exact (conj (conj H1 H2) H3). }
  apply (AR_laws_x_and_mem segs TfibB _ (@YG0dcf.arodata_ok_cf CfImg_B segs TfibB) ReplyKeptAroB.arodata_kept_B).
  apply AR_laws_x_and_hp.
  exact (AR_laws_x_cf (cp := CfParams_reply) segs TfibB (AR_laws_ok_cf (cp := CfParams_reply) segs TfibB)).
Qed.
Lemma ARX_rtW_hp0 : forall ly S Hp (W : world segs) mem md, TRL.ARX_rtW ly S Hp W mem md -> Hp = [].
Proof. intros ly S Hp W mem md H. exact (proj1 (proj2 H)). Qed.
Lemma topx_CSE_W : W_contract_x.cse_spec_x (PI := PB_fr) TfibB [] TRL.ARX_rtW
  (@pa_val _ fr_prog_listing PB_fr A_TEXT + AF_fr_check_shape_event).
Proof.
pose proof W_palib.pb_palib_tfib as TL.
pose proof ARX_rtW_laws as LAWS. pose proof ARX_rtW_hp0 as HP0.
pose proof TR3.topx_AMEMCHR_W as AMEMCHR. pose proof W_next_line.nl_objs_apart_fr as NLAP.
pose proof W_next_line.nl_crom_fr as HCROM.
(* each walk takes the Section hypotheses its proof uses (unused ones are discharged), so its premises are closed by
   type *)
assert (NL : W_contract_x.nl_spec_x (PI := PB_fr) TfibB [] TRL.ARX_rtW
  (@pa_val _ fr_prog_listing PB_fr A_TEXT + AF_fr_next_line))
  by (eapply (W_next_line.pb_next_line_x (PI := PB_fr) TfibB [] TRL.ARX_rtW); eassumption).
assert (CSD : W_contract_x.csd_spec_x (PI := PB_fr) TfibB [] TRL.ARX_rtW
  (@pa_val _ fr_prog_listing PB_fr A_TEXT + AF_fr_check_shape_done))
  by (eapply (W_check_shape_done.pb_check_shape_done_x (PI := PB_fr) TfibB [] TRL.ARX_rtW); eassumption).
pose proof TR2.topx_ASTRLEN_B_W as ASTRLEN. pose proof topx_ABCMP_W as ABCMP.
eapply (W_check_shape_event.pb_check_shape_event_x (PI := PB_fr) TfibB [] TRL.ARX_rtW); eassumption.
Qed.
End topx_cse_w.
