(* top_x's __asan_memcpy onto itself (a Theorem Labs lane): RR_x's Section hypothesis (W_relay_remove.v:131 and the W_rr_* files)
     AMEMCPYS : amemcpy_same_realizes_x B ARx (SIGMA WS_asan_memcpy)
   PROVED at the instance of A's top_x (W_LLVMFuzzerTestOneInput_top_x.v), B := TfibB and ARx := TopX_RT.ARX_rt (top_x's
   ARX verbatim, so the plug is `exact` up to unfolding ARX).  The proof is lib/A/AE6same_x.v's acpy_same_icpt (the walk
   of __asan_memcpy at 0x52728 with the destination equal to the source, ported from fuzz_disco's released
   lib/A/Rt/AcpySame.v) at ARx := ARX_rt, with the interceptor law record TopX_INTRIN.icpt_laws_ARX.  The statement
   W_sites_x.v:364 differs from acpy_same_icpt's only in form: its achecked premise is the conjunction of amem_range,
   range_addressable and the shadow hull (W_sites.v:82), the source is d itself, and its post is aentry_post_x with an
   empty write set: the bytes of [d, d + n) read the same after the call (each gets the byte it had) and every other byte
   outside the scratch window is unchanged.  Its rom_view, 8-byte range and not-in-image premises are not used.
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_kit_x W_journal_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AD2l CfImgA CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG0ncf YGcallcf YG0lawscf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_sites W_sites_x W_contract_x W_palib_fr.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import TopX_RT.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.TopX_INTRIN.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.AE6same_x.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Module TI := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.TopX_INTRIN.
Module MS := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.AE6same_x.

Section topx_memcpys. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PB_fr).

(* AMEMCPYS (W_relay_remove.v:131) at top_x's ARX *)
Lemma topx_AMEMCPYS : amemcpy_same_realizes_x TfibB ARX_rt (SIGMA WS_asan_memcpy).
Proof.
  rewrite TI.asan_memcpy_id_sigma.
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

(* QMm W1: AMEMCPYS at top_x's W1 relation TopX_RT.ARX_rtW (lib/A/W_LLVMFuzzerTestOneInput_top_x.v:180-182, which adds arodata_ok_cf). The rule at
   ARX_rt above, then the post rebuilt at ARX_rtW by TopX_RT.aentry_post_x_rtW: the write set is empty (the bytes of
   [d, d + n) read the same), so no kept byte is written, and the scratch window is ESTACK bytes above the image. *)
Lemma topx_AMEMCPYS_W : amemcpy_same_realizes_x TfibB ARX_rtW (SIGMA WS_asan_memcpy).
Proof.
  intros ly S Hp W regs mem md d n HPRE G10 G11 G12 Hn Hd Hdn HDST HSRC HCHK HROM H8 HIMG.
  destruct (ecall_pre_rtW _ _ _ _ _ _ _ HPRE) as (HPRE0 & HQ).
  eapply SRr_mono; [exact (topx_AMEMCPYS ly S Hp W regs mem md d n HPRE0 G10 G11 G12 Hn Hd Hdn HDST HSRC HCHK HROM H8 HIMG)|].
  intros W' c' _ HP.
  apply (aentry_post_x_rtW _ _ _ _ _ _ _ _ _ _ _ _ (proj1 HPRE0) HQ); [| | | exact HP].
  - destruct HPRE0 as (_ & _ & _ & Hlo & _). unfold ESTACK in Hlo. lia.
  - unfold ESTACK. lia.
  - intros a Ha. destruct Ha.
Qed.

End topx_memcpys.
