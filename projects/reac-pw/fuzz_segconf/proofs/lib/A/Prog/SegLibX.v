(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACfj.v (tfib_lib_x_body, tfib_lib_x) and lib/A/ACfi.v (XL0, tfib_lib_x_closed, tfib_lib_x_all) for plugin-hostd/fuzz_command: the program interface lib/A/ACfn.v (tfib_lib_contract_x at the library shape cmd_shape) is derived from the contract of the program's entry function, lib/A/Prog/LLVMFuzzerTestOneInput_c.v's tLLVMFuzzerTestOneInput_spec at the pinned image PB_cmd, instead of from cgif's segment walk; the entry's journal over the program's statics is widened to the interface's footprint (the statics and the sink token), and the sink, the meta cell, the file descriptors and the file system are kept by that journal (YE01.v's asink_none_kept and ameta_inv_kept, YCbq.v's aos_step_closed); the event bound of one call is lib/A/Prog/HarnessArgsEv.v's ev_ltoi_lib. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_command/lib/A/Prog/CmdLibX.v (origin/ossv/recipes 501c0d516c69) for reac-pw/fuzz_segconf's image A (fuzz_segconf.asan): module paths; Cmd*/cmd_* -> Seg*/seg_* (CmdShape.cmd_shape -> SegShape.seg_shape, CmdB -> SegB, CmdBSyms -> SegBSyms, GI_cmdA -> GI_segA, CMD_RLO / CMD_RHI -> SEG_RLO / SEG_RHI, cmd_PG -> seg_PG, HarnessArgsEv.ev_ltoi_lib -> SegHarnessEv.ev_ltoi_max); the entry's contract is segconf's lib/A/Prog/LLVMFuzzerTestOneInput_c.v LLVMFuzzerTestOneInput_contract (contracts FINAL 6f783602b5e3) taken at lib/A/Prog/SegInstA.v's image-A terms, in place of tLLVMFuzzerTestOneInput_spec at PB_cmd; its image premise seg_himg (the literals by translation unit, the box-model table, m_key.words / m_key.role, the stack-protector cells, longl, the cap multiplier) replaces fuzz_command's cmd_ro_ok / cmd_val_objs premises and is given at the call's state by lib/A/Prog/SegHimgA.v's seg_himg_at from the interface's read-only image (arodata_okS); the program's statics are segconf's one range, longl; the post carries no recorder invariant. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YC5d YCbp YE00 YE01 YO09 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.reac_pw.fuzz_segconf.images Require Import Asan.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require Import AB1v AF0m AE2k ACfn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require AD1u AD2l SegShape.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable SegSyms SegList SegAddr SegPa SegImg
  SegPgBase SegABase SegBase SegGlob SegObj SegRo.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require SegHarnessEv SegInstA SegHimgA.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import LLVMFuzzerTestOneInput_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
(* The guard (as lib/A/SegTop.v's): the plain build's sink hints are out of the way, so a bare sink_head resolves to
   the ASan image's own head AE2k.tfib_sink_head, the head the harness contract is stated at. *)
#[local] Remove Hints OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
#[local] Remove Hints OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable.YI5c.src0_sink : typeclass_instances.

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

(* segconf: the program's one static, longl, is not the sink token, nor a byte of the closed stdio environment
   (asink_none's bytes, AE2k.v), nor the meta cell (ameta_inv's) *)
Lemma seg_PG_closed : ~ YI16.sink_open_fp seg_PG.
Proof.
apply sink_closed_pos. unfold seg_PG, A_LONGL.
repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; lia.
Qed.
Lemma seg_PG_env : forall a, aclosed_env_addr tfib_K a -> ~ inFP seg_PG a.
Proof.
intros a Ha (r & Hr & Hlo). unfold aclosed_env_addr in Ha. cbn -[Z.add Z.lt Z.le] in Ha.
unfold A_threaded, A_need_locks, A_ofl_lock, FF_canary in Ha.
unfold seg_PG in Hr. cbn [In] in Hr.
destruct Hr as [<-|[]]; cbn [fst snd] in Hlo; unfold A_LONGL in Hlo; lia.
Qed.
Lemma seg_PG_meta : forall a, ak_meta_mem tfib_K <= a < ak_meta_mem tfib_K + 8 -> ~ inFP seg_PG a.
Proof.
intros a Ha (r & Hr & Hlo). cbn -[Z.add Z.lt Z.le] in Ha. unfold FF_meta_mem in Ha.
unfold seg_PG in Hr. cbn [In] in Hr.
destruct Hr as [<-|[]]; cbn [fst snd] in Hlo; unfold A_LONGL in Hlo; lia.
Qed.
Lemma seg_PG_incl : incl seg_PG (seg_PG ++ [sink_token]).
Proof. intros r Hr. apply in_or_app. left. exact Hr. Qed.
(* the live bytes of one call (LIVE_LTOI: c, m and the largest text block) are within the interface's LIVE_LIB *)
Lemma seg_live_le : LIVE_LTOI <= LIVE_LIB.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
(* the allocator events of one call (SegHarnessEv: at most 16) are within the interface's EV_LIB *)
Lemma seg_ev_lib : forall pl, EV_LTOI pl <= EV_LIB.
Proof.
intros pl. pose proof (SegHarnessEv.ev_ltoi_max pl) as H.
assert (E : SegHarnessEv.EV_LTOI_MAX <= EV_LIB) by (apply Z.leb_le; vm_compute; reflexivity). lia.
Qed.
(* the interface's addresses and window are SegInstA's (so the contract below is taken at the interface's numbers) *)
Lemma seg_acfn_terms : A_LLVMF = SegInstA.A_LLVMFuzzerTestOneInput_A /\ A_EMPTY = SegInstA.emptyA /\
  LLVMF_STK = SegInstA.STK_LLVMFuzzerTestOneInput /\ SEG_RLO = SegInstA.RLO_A /\ SEG_RHI = SegInstA.RHI_A.
Proof. vm_compute. repeat split; reflexivity. Qed.

Section x. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Existing Instance AE2k.tfib_sink_head | 0.
Variable B : asyms.
Variable MT : ameter_ops.
(* the allocator record (the core's; AD2l.SegB_syms for the pinned SegB) and the meter's laws *)
Hypothesis HB : SegBSyms B.
Hypothesis MTL : ameter_laws MT.
(* the meter the interface states, a function of the payload's length (cgif's XL, ACfj.v's HXL): it bounds the
   entry's own meter XM_LTOI at every payload of that length *)
Variable XL : Z -> Z.
Hypothesis HXL : forall pl : list byte, XM_LTOI MT pl <= XL (Z.of_nat (length pl)).
Variable j : nat.
(* segconf: the harness contract's image premise at the call's state is lib/A/Prog/SegHimgA.v's seg_himg_at, from
   the interface's read-only image (arodata_okS, as arodata_okP) and SegBSyms B. *)
Theorem seg_lib_x :
(forall fx0 : YK11.FPState, @LLVMFuzzerTestOneInput_contract fx0 rc AE2k.tfib_sink_head tfibsegs B MT
  SegInstA.A_LLVMFuzzerTestOneInput_A SegInstA.STK_LLVMFuzzerTestOneInput SegInstA.emptyA SegInstA.RLO_A
  SegInstA.RHI_A SegInstA.longlA SegInstA.mod40A SegInstA.catA SegInstA.wordsA SegInstA.rolesA SegInstA.gotwA
  SegInstA.guardA SegInstA.seg_litA_fz SegInstA.seg_litA_rc) ->
@tfib_lib_contract_x fx rc SegShape.seg_shape B MT XL XL SEG_RLO SEG_RHI GI_segA j.
Proof.
intros HSPEC ly S W regs mem md p n pl M K HAI HPRE HK.
destruct HPRE as (HPRE0 & HSTK & Hfrm & Hra & Hp & Hn & Hpn & Hnpl & HPL & Hfr0 & Hev & Hlive & HROS & HSNK & HFD & HSORT &
  HAM & HMOK & HGI).
pose proof (proj1 HPRE0) as HAR.
(* the program statement's pre-condition *)
assert (HROP : arodata_okP tfibsegs SEG_RLO SEG_RHI B (aview tfibsegs (w_H W) mem)) by (intros a Ha; exact (HROS a Ha)).
pose proof (SegHimgA.seg_himg_at B HB ly S W mem md HAR HROP) as HIMG.
assert (HXLp : XM_LTOI MT pl <= XL n) by (rewrite Hnpl; exact (HXL pl)).
assert (HMOK' : mo_ok MT S (XM_LTOI MT pl)) by exact (mo_ok_le MT MTL S _ _ HMOK HXLp).
(* the allocator events of one call are within the interface's EV_LIB (SegHarnessEv.v: at most 16) *)
pose proof (seg_ev_lib pl) as HEVp.
assert (HEV' : st_nev S + EV_LTOI pl <= EV_MAX) by lia.
assert (HLIVE' : blocks_bytes S + LIVE_LTOI <= LIVE_MAX) by (pose proof seg_live_le; lia).
pose proof (HSPEC fx ly S W regs mem md [] p n pl j HPRE0 HSTK Hfrm HROP HIMG Hp Hn Hpn Hnpl HPL Hfr0 HGI HEV' HLIVE'
  HMOK') as HSRr.
match type of HSRr with SRr _ _ (cfg_at _ ?a _ _ _) _ => replace a with A_LLVMF in HSRr by reflexivity end.
(* the return *)
assert (ERA : getr regs 1 = w64 RA_LLVMF) by (unfold w64; rewrite <- Hra; unfold raZ; symmetry; apply Z_to_bv_bv_unsigned).
change (@LIBK SegShape.seg_shape pl (m_fs md) K) with (K (LL 0 (m_fs md) [])).
refine (SRr_srealizes tfibsegs W (cfg_at tfibsegs A_LLVMF regs mem md) _ (K (LL 0 (m_fs md) [])) HSRr HAI _).
intros W' c' Hwle HAI' (fx' & ly' & S' & regs' & mem' & md' & Ec & Hfrr & Hcsr & HJ & HRP & HR10 & HPERM & HPAY & HGI' &
  HMLE & HBB).
(* the contract states its journal at the harness's own names, ltoi_PG longlA and STK_LLVMFuzzerTestOneInput, which are
   seg_PG and LLVMF_STK by definition (A_LONGL, 121; 32768) *)
change (ltoi_PG SegInstA.longlA) with seg_PG in HJ. change SegInstA.STK_LLVMFuzzerTestOneInput with LLVMF_STK in HJ.
pose proof HJ as (_ & _ & _ & _ & Hos & _).
destruct (aos_step_closed seg_PG md md' seg_PG_closed Hos) as (Efd & Efsys & _ & _).
apply (HK (LL 0 (m_fs md) []) W' c' Hwle HAI').
exists fx', ly', S', regs', mem', md', (EV_LTOI pl).
split; [rewrite Ec; unfold cfg_at; rewrite ERA; reflexivity|].
split; [exact Hfrr|]. split; [exact Hcsr|].
split.
{ exact (ajournal_fp_incl tfibsegs B LLVMF_STK (spZ regs) seg_PG (seg_PG ++ [sink_token]) ly S W mem md [] ly' S' W' mem'
    md' (EV_LTOI pl) HJ seg_PG_incl). }
split; [exact HEVp|].
split; [exact HRP|]. split; [exact HR10|]. split; [exact HPERM|].
split; [intros fd; unfold m_fds; rewrite Efd; reflexivity|].
split; [cbn [ll_fs]; unfold m_fs; rewrite Efsys; reflexivity|].
split; [reflexivity|]. split; [reflexivity|]. split; [exact HSORT|].
split.
{ exact (asink_none_kept tfibsegs B tfib_K (AD1u.tfib_AIL B HB) LLVMF_STK (spZ regs) seg_PG ly S W mem md [] ly' S' W' mem'
    md' (EV_LTOI pl) HJ seg_PG_closed seg_PG_env HSNK). }
split.
{ exact (ameta_inv_kept tfibsegs B tfib_K (AD1u.tfib_AIL B HB) LLVMF_STK (spZ regs) seg_PG ly S W mem md [] ly' S' W' mem'
    md' (EV_LTOI pl) M HJ seg_PG_meta HAM). }
split; [exact (mo_le_mono MT MTL S S' _ _ HMLE HXLp)|].
split; [exact HPAY | exact HGI'].
Qed.
End x.

(* the trivial meter (cgif's ACfi.v XL0): no bound *)
Definition XL0 : Z -> Z := fun _ => 0.
Lemma XL0_HXL : forall pl : list byte, XM_LTOI ameter_triv pl <= XL0 (Z.of_nat (length pl)).
Proof. intros pl. unfold XM_LTOI, XL0. cbn [mo_malloc mo_free ameter_triv]. lia. Qed.

(* The interface at the pinned allocator record SegB and the trivial meter, at every FP state. What remains is the
   contract of the program's entry function at every FP state (SegProgClosed.v's seg_ltoi_all, from the walks). *)
Section closed. Context {rc : YM05.RunCeil}.
Hypothesis HLTOI : forall fx0 : YK11.FPState, @LLVMFuzzerTestOneInput_contract fx0 rc AE2k.tfib_sink_head tfibsegs
  AD2l.SegB ameter_triv SegInstA.A_LLVMFuzzerTestOneInput_A SegInstA.STK_LLVMFuzzerTestOneInput SegInstA.emptyA
  SegInstA.RLO_A SegInstA.RHI_A SegInstA.longlA SegInstA.mod40A SegInstA.catA SegInstA.wordsA SegInstA.rolesA
  SegInstA.gotwA SegInstA.guardA SegInstA.seg_litA_fz SegInstA.seg_litA_rc.
Theorem seg_lib_x_closed : forall j : nat,
  @tfib_lib_contract_x_all rc SegShape.seg_shape AD2l.SegB ameter_triv XL0 XL0 SEG_RLO SEG_RHI GI_segA j.
Proof.
intros j fx.
exact (@seg_lib_x fx rc AD2l.SegB ameter_triv AD2l.SegB_syms ameter_triv_laws XL0 XL0_HXL j HLTOI).
Qed.
End closed.
