(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACfj.v (tfib_lib_x_body, tfib_lib_x) and lib/A/ACfi.v (XL0, tfib_lib_x_closed, tfib_lib_x_all) for plugin-hostd/fuzz_command: the program interface lib/A/ACfn.v (tfib_lib_contract_x at the library shape cmd_shape) is derived from the contract of the program's entry function, lib/A/Prog/LLVMFuzzerTestOneInput_c.v's tLLVMFuzzerTestOneInput_spec at the pinned image PB_cmd, instead of from cgif's segment walk; the entry's journal over the program's statics is widened to the interface's footprint (the statics and the sink token), and the sink, the meta cell, the file descriptors and the file system are kept by that journal (YE01.v's asink_none_kept and ameta_inv_kept, YCbq.v's aos_step_closed); the event bound of one call is lib/A/Prog/HarnessArgsEv.v's ev_ltoi_lib. *)
(* Modified by Theorem Labs, 2026-10: twin of an earlier version of lib/A/Prog/CmdLibX.v for the ASan+UBSan build fuzz_command.asan-ubsan: module paths A -> B, image Asan -> AsanUbsan, core files AB1v / AF0m / AE2k / ACfn / AD1u / AD2l -> YB1v / YF0m / YE2k / YCfn / YD1u / YD2l (the image-B twins, same identifiers); the library shape is written as its definition (AgreeShape.ag_shape ZTraceSpec.checksum_shape, the body of lib/A/CmdShape.v's cmd_shape) so that no lib/B file Requires lib/A; B's interface pre (lib/B/YCfn.v) and entry contract (lib/B/Prog/LLVMFuzzerTestOneInput_c.v) carry no astack_pres conjunct (A's pass 5b is A-only), so the pre has one conjunct fewer and the contract one premise fewer. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04 YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YCbp YE00 YE01 YO09 YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YG0q.
From OSSVerify.plugin_hostd.fuzz_command.images Require Import AsanUbsan.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YB1v YF0m YE2k YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require YD1u YD2l.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require ZTraceSpec AgreeShape.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdAddr CmdPa CmdImg
  CmdBase CmdGlob CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require CmdRecImg CmdRecRo CmdRecRest HarnessArgsEv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import LLVMFuzzerTestOneInput_c.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* the library shape of fuzz_command's agreement statements, lib/A/CmdShape.v's cmd_shape written as its body *)
#[local] Notation cmd_shape := (AgreeShape.ag_shape ZTraceSpec.checksum_shape).

(* A journal over a footprint is a journal over any larger footprint, whether or not the larger one holds the sink
   token (PaCallPg.v's ajournal_fp_widen asks the larger footprint to be closed; the interface's footprint
   cmd_PG ++ [sink_token] is open). *)
Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Lemma ajournal_fp_incl : forall STK sp0 FP FP' ly S W mem md own ly' S' W' mem' md' k,
ajournal segs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
incl FP FP' ->
ajournal segs B STK sp0 FP' ly S W mem md own ly' S' W' mem' md' k.
Proof.
intros STK sp0 FP FP' ly S W mem md own ly' S' W' mem' md' k
(HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstk & F5 & HQT) HI.
assert (HS : YI16.sink_open_fp FP -> YI16.sink_open_fp FP') by exact (sink_open_mono FP FP' HI).
assert (HN : forall a, ~ inFP FP' a -> ~ inFP FP a) by (intros a Hn Hf; exact (Hn (inFP_mono FP FP' a HI Hf))).
split; [exact HAR|]. split; [exact Hly|]. split; [exact Hsecs|]. split; [exact Hwle|].
split; [exact (aos_step_mono FP FP' md md' HS Hio)|].
split; [exact Hfrs|]. split; [exact Hnev|]. split; [exact Hk|].
split; [intros a Ha Hs Hn; exact (F1 a Ha Hs (HN a Hn))|].
split; [intros p n i H1 H2 Hi Hn; exact (F2 p n i H1 H2 Hi (HN _ Hn))|].
split; [intros a Hi Ho He Hsp; exact (F3 a Hi Ho He (fp_spares_mono FP FP' a HI Hsp))|].
split; [intros cid pos a Hin Hr Hn; exact (F4 cid pos a Hin Hr (HN a Hn))|].
split; [intros p n i H1 H2 Hi; exact (inFP_mono FP FP' _ HI (Hgone p n i H1 H2 Hi))|].
split; [exact Hpres|]. split; [exact Hstk|]. split; [exact F5 | exact HQT].
Qed.
End w.

(* The program's statics (g_rec, record.spill, g_quitting) are not the sink token, nor a byte of the closed stdio
   environment (asink_none's bytes, YE2k.v), nor the meta cell (ameta_inv's) *)
Lemma cmd_PG_closed : ~ YI16.sink_open_fp cmd_PG.
Proof.
apply sink_closed_pos. unfold cmd_PG, A_G_REC, A_REC_SPILL, A_G_QUITTING.
repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; lia.
Qed.
Lemma cmd_PG_env : forall a, aclosed_env_addr tfib_K a -> ~ inFP cmd_PG a.
Proof.
intros a Ha (r & Hr & Hlo). unfold aclosed_env_addr in Ha. cbn -[Z.add Z.lt Z.le] in Ha.
unfold A_threaded, A_need_locks, A_ofl_lock, FF_canary in Ha.
unfold cmd_PG in Hr. cbn [In] in Hr.
destruct Hr as [<-|[<-|[<-|[]]]]; cbn [fst snd] in Hlo; unfold A_G_REC, A_REC_SPILL, A_G_QUITTING in Hlo; lia.
Qed.
Lemma cmd_PG_meta : forall a, ak_meta_mem tfib_K <= a < ak_meta_mem tfib_K + 8 -> ~ inFP cmd_PG a.
Proof.
intros a Ha (r & Hr & Hlo). cbn -[Z.add Z.lt Z.le] in Ha. unfold FF_meta_mem in Ha.
unfold cmd_PG in Hr. cbn [In] in Hr.
destruct Hr as [<-|[<-|[<-|[]]]]; cbn [fst snd] in Hlo; unfold A_G_REC, A_REC_SPILL, A_G_QUITTING in Hlo; lia.
Qed.
Lemma cmd_PG_incl : incl cmd_PG (cmd_PG ++ [sink_token]).
Proof. intros r Hr. apply in_or_app. left. exact Hr. Qed.
(* the live bytes of one call (LIVE_LTOI: the recorder's blocks, the three words blocks, a callee's peak) are within
   the interface's LIVE_LIB *)
Lemma cmd_live_le : LIVE_LTOI <= LIVE_LIB.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.

Section x. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Existing Instance YE2k.tfib_sink_head | 0.
Variable B : asyms.
Variable MT : ameter_ops.
(* the allocator record (the image-B core's; YD2l.CmdB_syms for the pinned CmdB) and the meter's laws *)
Hypothesis HB : CmdBSyms B.
Hypothesis MTL : ameter_laws MT.
(* the meter the interface states, a function of the payload's length (cgif's XL, ACfj.v's HXL): it bounds the
   entry's own meter XM_LTOI at every payload of that length *)
Variable XL : Z -> Z.
Hypothesis HXL : forall pl : list byte, XM_LTOI MT pl <= XL (Z.of_nat (length pl)).
Variable j : nat.
Theorem cmd_lib_x :
(forall fx0 : YK11.FPState, @tLLVMFuzzerTestOneInput_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT) ->
@tfib_lib_contract_x fx rc cmd_shape B MT XL XL CMD_RLO CMD_RHI GI_cmdA j.
Proof.
intros HSPEC ly S W regs mem md p n pl M K HAI HPRE HK.
destruct HPRE as (HPRE0 & Hfrm & Hra & Hp & Hn & Hpn & Hnpl & HPL & Hfr0 & Hev & Hlive & HROS & HSNK & HFD & HSORT &
  HAM & HMOK & HGI).
pose proof (proj1 HPRE0) as HAR.
(* the program statement's pre-condition *)
assert (HROP : arodata_okP tfibsegs CMD_RLO CMD_RHI B (aview tfibsegs (w_H W) mem)) by (intros a Ha; exact (HROS a Ha)).
assert (HROK : cmd_ro_ok (aview tfibsegs (w_H W) mem)).
{ exact (CmdRecRo.cmd_ro_ok_of_aro tfibsegs B (YG0q.AR_laws_ok tfibsegs B) HB (CmdRecImg.cmd_img_facts_tfib B HB)
    ly S W mem md HAR HROP). }
assert (HXLp : XM_LTOI MT pl <= XL n) by (rewrite Hnpl; exact (HXL pl)).
assert (HMOK' : mo_ok MT S (XM_LTOI MT pl)) by exact (mo_ok_le MT MTL S _ _ HMOK HXLp).
(* the allocator events of one call are within the interface's EV_LIB (lib/B/Prog/HarnessArgsEv.v: at most 2,505) *)
pose proof (HarnessArgsEv.ev_ltoi_lib pl) as HEVp.
assert (HEV' : st_nev S + EV_LTOI pl <= EV_MAX) by lia.
assert (HLIVE' : blocks_bytes S + LIVE_LTOI <= LIVE_MAX) by (pose proof cmd_live_le; lia).
pose proof (HSPEC fx ly S W regs mem md [] p n pl j HPRE0 Hfrm HROP HROK CmdRecRest.cmd_val_objs_PB Hp Hn Hpn Hnpl HPL
  Hfr0 HGI HEV' HLIVE' HMOK') as HSRr.
match type of HSRr with SRr _ _ (cfg_at _ ?a _ _ _) _ => replace a with A_LLVMF in HSRr by reflexivity end.
(* the return *)
assert (ERA : getr regs 1 = w64 RA_LLVMF) by (unfold w64; rewrite <- Hra; unfold raZ; symmetry; apply Z_to_bv_bv_unsigned).
change (@LIBK cmd_shape pl (m_fs md) K) with (K (LL 0 (m_fs md) [])).
refine (SRr_srealizes tfibsegs W (cfg_at tfibsegs A_LLVMF regs mem md) _ (K (LL 0 (m_fs md) [])) HSRr HAI _).
intros W' c' Hwle HAI' (fx' & ly' & S' & regs' & mem' & md' & Ec & Hfrr & Hcsr & HJ & HRP & HR10 & HPERM & HPAY & HREC &
  HGI' & HMLE & HBB).
pose proof HJ as (_ & _ & _ & _ & Hos & _).
destruct (aos_step_closed cmd_PG md md' cmd_PG_closed Hos) as (Efd & Efsys & _ & _).
apply (HK (LL 0 (m_fs md) []) W' c' Hwle HAI').
exists fx', ly', S', regs', mem', md', (EV_LTOI pl).
split; [rewrite Ec; unfold cfg_at; rewrite ERA; reflexivity|].
split; [exact Hfrr|]. split; [exact Hcsr|].
split.
{ exact (ajournal_fp_incl tfibsegs B LLVMF_STK (spZ regs) cmd_PG (cmd_PG ++ [sink_token]) ly S W mem md [] ly' S' W' mem'
    md' (EV_LTOI pl) HJ cmd_PG_incl). }
split; [exact HEVp|].
split; [exact HRP|]. split; [exact HR10|]. split; [exact HPERM|].
split; [intros fd; unfold m_fds; rewrite Efd; reflexivity|].
split; [cbn [ll_fs]; unfold m_fs; rewrite Efsys; reflexivity|].
split; [reflexivity|]. split; [reflexivity|]. split; [exact HSORT|].
split.
{ exact (asink_none_kept tfibsegs B tfib_K (YD1u.tfib_AIL B HB) LLVMF_STK (spZ regs) cmd_PG ly S W mem md [] ly' S' W' mem'
    md' (EV_LTOI pl) HJ cmd_PG_closed cmd_PG_env HSNK). }
split.
{ exact (ameta_inv_kept tfibsegs B tfib_K (YD1u.tfib_AIL B HB) LLVMF_STK (spZ regs) cmd_PG ly S W mem md [] ly' S' W' mem'
    md' (EV_LTOI pl) M HJ cmd_PG_meta HAM). }
split; [exact (mo_le_mono MT MTL S S' _ _ HMLE HXLp)|].
split; [exact HPAY | exact HGI'].
Qed.
End x.

(* the trivial meter (cgif's ACfi.v XL0): no bound *)
Definition XL0 : Z -> Z := fun _ => 0.
Lemma XL0_HXL : forall pl : list byte, XM_LTOI ameter_triv pl <= XL0 (Z.of_nat (length pl)).
Proof. intros pl. unfold XM_LTOI, XL0. cbn [mo_malloc mo_free ameter_triv]. lia. Qed.

(* The interface at the pinned allocator record CmdB and the trivial meter, at every FP state. What remains is the
   contract of the program's entry function at every FP state (B's lib/B/Prog/LLVMFuzzerTestOneInput_c.v; its
   closing file is the B top-level walk's LLVMFuzzerTestOneInputClosed.v, on another branch, at CmdB, YD2l.CmdB_syms and
   the trivial meter's laws, from the callees' and the runtime entries' contracts). *)
Section closed. Context {rc : YM05.RunCeil}.
Hypothesis HLTOI : forall fx0 : YK11.FPState,
  @tLLVMFuzzerTestOneInput_spec fx0 rc YE2k.tfib_sink_head PB_cmd YD2l.CmdB ameter_triv.
Theorem cmd_lib_x_closed : forall j : nat,
  @tfib_lib_contract_x_all rc cmd_shape YD2l.CmdB ameter_triv XL0 XL0 CMD_RLO CMD_RHI GI_cmdA j.
Proof.
intros j fx.
exact (@cmd_lib_x fx rc YD2l.CmdB ameter_triv YD2l.CmdB_syms ameter_triv_laws XL0 XL0_HXL j HLTOI).
Qed.
End closed.
