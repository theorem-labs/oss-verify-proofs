(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: pins_set's ASan walk assembled from its pieces (lib/A/Prog/pins_set_s1.v ..
   pins_set_s13.v), after proofs/cgif/cgif_file_fuzzer/lib/A/AChf.v (cgif_close's walk assembled from its segments). *)

(* tpins_set_holds: the statement of lib/A/Prog/pins_set_c.v. The walk runs
   entry (ps_seg_entry, both arms of record()) -> join (ps_join) -> xstrdup 1 .. 3 and the stores after them
   (ps_seg_x) -> the fourth store, the refuse test, mix_call and the tail jump into answer_code (ps_seg_x4, with
   ps_store, ps_close and ps_tail). The three string arguments the statement gives as heap blocks are astr_argA's
   block arm. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YG0s YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05 YC5d YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdAddr CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaCall PaCallRun PaLibF PaLibG PaLibH PaSB PaDenot.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
rec_calls_free_c xstrdup_c mix_call_c answer_code_c pins_set_c hand_back_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
RecBLemmas pins_set_s2 pins_set_s1 pins_set_s3 pins_set_s4 pins_set_s5 pins_set_s6 pins_set_s7 pins_set_s8.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
pins_set_s9 pins_set_s10 pins_set_s11 pins_set_s12 pins_set_s13.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
#[local] Notation LAWS := (AR_laws_ok SEGS B).

(* a string the statement gives as a heap block (pins_set_c.v:100-108) is astr_argA's block arm *)
Lemma ps_blk_arg : forall ly S (W : world SEGS) mem md O p x,
AR SEGS B ly S W mem md ->
in_blockA (ablocks B ly S) p (Z.of_nat (length x) + 1) ->
Forall (fun qk => iv_apart p (Z.of_nat (length x) + 1) (fst qk) (snd qk)) O ->
astr_atR (rdW W mem) p x -> Z.of_nat (length x) + 1 <= LMAX + 1 ->
astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O p (Some x).
Proof.
intros ly S W mem md O p x HAR Hblk HapO Hstr Hn.
destruct Hblk as (q & m & Hqm & Hq1 & Hq2) eqn:Eb.
destruct (al_blocks _ _ LAWS _ _ _ _ _ q m HAR Hqm) as (_ & H4096 & _).
split; [lia|]. split; [exact Hstr|]. split; [exact Hn|].
left. split; [exists q, m; split; [exact Hqm | lia] | exact HapO].
Qed.

(* the statement's Section hypotheses (pins_set_c.v:76-81): the callees' contracts at every FP state *)
Hypothesis TRCF : forall fx0 : YK11.FPState, @trec_calls_free_spec fx0 rc SK PI B MT.
Hypothesis TXSTRDUP : forall fx0 : YK11.FPState, @txstrdup_spec fx0 rc SK PI B MT.
Hypothesis TMIX_CALL : forall fx0 : YK11.FPState, @tmix_call_spec fx0 rc SK PI B MT.
Hypothesis TANSWER_CODE : forall fx0 : YK11.FPState, @tanswer_code_spec fx0 rc SK PI B MT.
Hypothesis VOBJS : cmd_val_objs.
(* the per-binary facts the statement does not carry yet, with the statements' names and forms, shared by every
   recorder walk (each to become a lemma of lib/A/Prog/CmdRecFacts.v) *)
Hypothesis MTL : ameter_laws MT.
Hypothesis HB : CmdBSyms B.
Hypothesis TL : PALib B.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis cmd_prog_img : forall a, Exists (in_zr a) recb_PG -> in_img SEGS a.
Hypothesis cmd_prog_writable : forall ly S (W : world SEGS) mem md a,
AR SEGS B ly S W mem md -> Exists (in_zr a) recb_PG -> writable_at SEGS (mrestrict (w_H W) mem) a.
Hypothesis RRO : ro_below_ofl SEGS RLO RHI.
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> in_img SEGS a.
Hypothesis cmd_ro_ok_of_aro : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem).
Hypothesis cmd_ro_prog_apart : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a /\ ~ Exists (in_zr a) recb_PG.
Hypothesis cmd_heap_tail_vis : forall ly S (W : world SEGS) mem md p n e, AR SEGS B ly S W mem md ->
In (p, n) (ablocks B ly S) -> p <= e < p + n -> atail_vis SEGS W mem e.
Hypothesis CMD_RO_IN : cmd_ro_in (in_roP SEGS CMD_RLO CMD_RHI).

Theorem tpins_set_holds : tpins_set_spec B MT.
Proof.
unfold tpins_set_spec.
intros ly S W regs mem md ch pu pf pl pv u f l verdict R O HPRE HRM HROD HROOK H10 HPU H11 HPF H12 HPL H13 HPV
  Bu Au Su Lu Bf Af Sf Lf Bl Al Sl Ll HSV HTV HREPA HFRM HEV HLIVE HMOK.
pose proof HPRE as (HAR & _).
pose proof (ps_blk_arg ly S W mem md O pu u HAR Bu Au Su Lu) as HSU.
pose proof (ps_blk_arg ly S W mem md O pf f HAR Bf Af Sf Lf) as HSF.
pose proof (ps_blk_arg ly S W mem md O pl l HAR Bl Al Sl Ll) as HSL.
pose proof (ps_store B MT ly S W regs mem md ch (Some u) (Some f) (Some l) verdict R O HPRE) as PSTORE.
pose proof (ps_close B MT ly S W regs mem md pu pf pl pv (Some u) (Some f) (Some l) verdict R O HSU HSF HSL HSV)
  as PCLOSE.
pose proof (ps_tail B MT MTL HB cmd_prog_img RRO RELRO_IMG cmd_ro_ok_of_aro cmd_ro_prog_apart (TANSWER_CODE fx)
  ly S W regs mem md ch (Some u) (Some f) (Some l) verdict R O HPRE HRM HROD HREPA HEV HLIVE HMOK HFRM) as PTAIL.
pose proof (ps_seg_x4 B MT (TMIX_CALL fx) HB VOBJS SIGP cmd_prog_img cmd_prog_writable RRO RELRO_IMG cmd_ro_ok_of_aro
  cmd_ro_prog_apart ly S W regs mem md ch pf pl pv (Some u) (Some f) (Some l) verdict R O HPRE HROD HREPA HEV
  PSTORE PCLOSE PTAIL) as X4.
pose proof (ps_seg_x B MT (TXSTRDUP fx) MTL HB cmd_prog_img RRO RELRO_IMG cmd_ro_ok_of_aro cmd_ro_prog_apart
  cmd_heap_tail_vis CMD_RO_IN VOBJS SIGP cmd_prog_writable ly S W regs mem md ch pu pf pl pv (Some u) (Some f) (Some l)
  verdict R O HPRE HROD HSU HSF HSL HSV HREPA HEV HLIVE HMOK) as SEGX.
pose proof (SEGX 3%nat ltac:(lia) X4) as X3.
pose proof (SEGX 2%nat ltac:(lia) X3) as X2.
pose proof (SEGX 1%nat ltac:(lia) X2) as X1.
pose proof (ps_join B MT (TXSTRDUP fx) MTL HB cmd_prog_img RRO RELRO_IMG cmd_ro_ok_of_aro cmd_ro_prog_apart
  cmd_heap_tail_vis CMD_RO_IN VOBJS SIGP cmd_prog_writable ly S W regs mem md ch pu pf pl pv (Some u) (Some f) (Some l)
  verdict R O HPRE HROD HSU HSF HSL HSV HREPA HEV HLIVE HMOK HPU X1) as JC.
exact (ps_seg_entry B MT MTL HB cmd_prog_img RRO RELRO_IMG cmd_ro_prog_apart (TRCF fx) VOBJS TL SIGP cmd_prog_writable
  ly S W regs mem md ch pu pf pl pv (Some u) (Some f) (Some l) verdict R O HPRE HROD HREPA HEV HMOK
  H10 H11 H12 H13 JC).
Qed.

End e.
End f.
End d.
