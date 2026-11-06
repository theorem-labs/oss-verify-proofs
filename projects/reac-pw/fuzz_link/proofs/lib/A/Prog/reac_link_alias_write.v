(* reac_link_alias_write (fuzz_link.asan 0x88f54, listing offset AF_reac_link_alias_write = 0x6d88, 1252 bytes)
   on image A: the top of its walk. The contract is lib/A/Prog/reac_link_alias_write_c.v
   `reac_link_alias_write_acontract` (the `aleaf_rd` shape of lib/A/Prog/link_amem.v, over the caller's
   program-global journal `ajournal_gx`).

   The walk is cut at three places (lib/A/Prog/reac_link_alias_writeDefs.v) and proved in four files:
     reac_link_alias_writeHead.v  `aw_head : aw_mid_obl -> the contract`    +0x00 .. +0x1a8, the 96-byte frame,
                                                                           the realigned sp, frame_alloc_3, F's
                                                                           header and its 64 shadow bytes
     reac_link_alias_writeArms*.v `aw_arms : aw_exit_obl -> aw_send_obl -> aw_mid_obl`
                                                                           +0x1a8 .. +0x1f0, the five refusal
                                                                           arms, wrapper_strlen and
                                                                           fuzz_if_nametoindex
     reac_link_alias_writeSend*.v `aw_send : aw_exit_obl -> aw_send_obl`    +0x1f0 .. +0x3a4, the request in the
                                                                           frame, checked_memset,
                                                                           checked_memcpy and nl_talk
     reac_link_alias_writeExit.v  `aw_exit : aw_exit_obl`                   +0x3a4 .. +0x4d0, the retired magic,
                                                                           meta_fill_f5, the inline release of
                                                                           the frame's flag byte, the epilogue,
                                                                           and the contract's whole post
   `aw_shape` below is the proof that the cut loses nothing: a walk that reaches `aw_post cx` from every `cx`
   whose `aw_pre` holds IS the contract. `reac_link_alias_write_aproof` composes the four pieces.

   Proves function reac_link_alias_write (image A, the asan build). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import nl_talk_c reac_link_alias_write_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalk PcapRelro PcapRelroA.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import reac_link_alias_writeDefs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import fuzz_if_nametoindex_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require RtString.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import SetShadowDef.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require
  reac_link_alias_writeHead reac_link_alias_writeArmsD reac_link_alias_writeSend reac_link_alias_writeExit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
Variable B : asyms.
Hypothesis LV : LinkVals.

(* The entry configuration of the contract, at a context. *)
Definition aw_cfg (cx : awcx) : config :=
  cfg_at SEGS REAC_LINK_ALIAS_WRITE_A (aw_regs cx) (aw_memc cx) (aw_mdc cx).

(* THE INTERFACE IS THE CONTRACT. `aleaf_rd`'s body, at the context the walk carries, is exactly
   `aw_pre cx -> SRr SEGS (aw_W cx) (aw_cfg cx) (aw_post cx)`: the three premises of the shape are the three
   conjuncts of `aw_pre`, and its conclusion is `aw_post`. *)
Theorem aw_shape :
  (forall cx : awcx, aw_pre SK B cx -> SRr SEGS (aw_W cx) (aw_cfg cx) (aw_post SK B cx)) ->
  reac_link_alias_write_acontract SK SEGS PCAP_RLO PCAP_RHI B.
Proof.
intros H G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HPRE HRD HP.
exact (H (mkAWCX G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs)
         (conj HPRE (conj HRD HP))).
Qed.

(* and back: a walk that proves the contract gives the interface's shape, so the cut loses nothing *)
Theorem aw_shape_rev :
  reac_link_alias_write_acontract SK SEGS PCAP_RLO PCAP_RHI B ->
  forall cx : awcx, aw_pre SK B cx -> SRr SEGS (aw_W cx) (aw_cfg cx) (aw_post SK B cx).
Proof.
intros H cx (HPRE & HRD & HP). destruct cx. exact (H _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HPRE HRD HP).
Qed.

End b.
End a.

(* The instance fact the four pieces take as `RELRO_IMG`, discharged here once, where the image is in scope:
   the read-only window of lib/A/Prog/PcapRelro.v lies inside one loaded segment, so each of its bytes is an
   image byte, which is what `akept`'s image clause needs to carry `arodata_okP` across a step. `tfibsegs`
   (lib/A/AB1v.v) is `Asan.M.loaded_segments`, the segments lib/A/Prog/LinkPaCheck.v certifies the listing
   against; the link `PAImg` instance has `pa_segs = tfibsegs` by reflexivity (the `HSEGS` convention). *)
Lemma aw_relro_img_tfib : forall a, PCAP_RLO <= a < PCAP_RHI -> in_img tfibsegs a.
Proof.
intros a Ha. destruct pcap_relro_in_image as (s & Hin & H1 & H2 & H3).
exists s. split; [exact Hin | lia].
Qed.

(* No global sink_head instance is in scope here. *)
Fail Definition sink_head_probe_top : YI16.sink_head := _.

(* ==========================================================================
   THE PROOF of reac_link_alias_write on image A: the four pieces composed.
   ========================================================================== *)
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section d.
Context {PI : PAImg link_listing}.
Variable B : asyms.
(* the allocator's laws at link's B: lib/A/PcapBFacts.v PcapB_LAWS *)
Hypothesis LAWS : AR_laws pa_segs B.
(* the listing's values at the image: lib/A/Prog/LinkImgInst.v pi_link_vals *)
Hypothesis LV : LinkVals.
(* the image's GOT / cell objects at B: LinkPaLib.v PALib, at link's B *)
Hypothesis TL : PALib B.
(* the image's symbols (lib/A/AF0m.v PcapSyms): AD2l.PcapB_syms *)
Hypothesis TB : AF0m.PcapSyms B.
(* the segments the listing is certified against: LinkImgInst.v pi_link_segs, by reflexivity *)
Hypothesis HSEGS : pa_segs = tfibsegs.
(* frame_alloc_3 (0x3dc18): lib/A/Rt/StackSideInst.v link_stack_malloc_3 *)
Hypothesis ASM3 : astack_malloc_realizes pa_segs B 3.
(* meta_fill_f5 (0x55f7c): lib/A/Rt/SetShadow.v link_set_shadow_f5 *)
Hypothesis ASS : aset_shadow_realizes pa_segs B (pa_sigma LS___asan_set_shadow_f5) 0xf5.
(* wrapper_strlen (0x43044): lib/A/Rt/RtClosed.v cmd_strlen_closed *)
Hypothesis ASTRLEN : RtString.astrlen_realizes pa_segs B (pa_sigma LS___interceptor_trampoline_strlen).
(* checked_memset (0x53214) / checked_memcpy (0x52d78): lib/A/AE2r.v asan_memset_realizes,
   lib/A/AE2q.v asan_memcpy_realizes *)
Hypothesis AMSET : aintrin_realizes pa_segs B OSet (pa_sigma LS___asan_memset).
Hypothesis AMCPY : aintrin_realizes pa_segs B OCpy (pa_sigma LS___asan_memcpy).
(* the two own callees: fuzz_if_nametoindex (0x826cc) and nl_talk
   (0x88974) *)
Hypothesis NIX : fuzz_if_nametoindex_acontract SK pa_segs PCAP_RLO PCAP_RHI B.
Hypothesis NLT : nl_talk_acontract SK pa_segs PCAP_RLO PCAP_RHI B.

Theorem reac_link_alias_write_aproof : reac_link_alias_write_acontract SK pa_segs PCAP_RLO PCAP_RHI B.
Proof.
assert (RELRO_IMG : forall a, PCAP_RLO <= a < PCAP_RHI -> in_img pa_segs a).
{ intros a Ha. rewrite HSEGS. exact (aw_relro_img_tfib a Ha). }
assert (EX : aw_exit_obl SK B) by (eapply (reac_link_alias_writeExit.aw_exit SK B); eassumption).
assert (SE : aw_send_obl SK B) by (eapply (reac_link_alias_writeSend.aw_send SK B); eassumption).
assert (MI : aw_mid_obl SK B) by (eapply (reac_link_alias_writeArmsD.aw_arms SK B); eassumption).
eapply (reac_link_alias_writeHead.aw_head SK B); eassumption.
Qed.

End d.
End c.

About reac_link_alias_write_aproof.
Print Assumptions reac_link_alias_write_aproof.
