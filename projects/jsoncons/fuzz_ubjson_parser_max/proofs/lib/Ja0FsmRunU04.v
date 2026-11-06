(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib MemSplit As0StepLib Ja0RegionPoisoned Ja0TlsGetAddr Ja0FakeStackGC Ja0FakeStackGCC
Ja0Fsm0Gen Ja0Fsm4Gen Ja0Fsm0Post Ja0Fsm4Post Ja0Fsm0Run Ja0Fsm4Run Ja0FsmRunU.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Ltac pw e := let v := eval vm_compute in e in change e with v.
Lemma fsm_run_u_0 : fsm_run_u 0 (0x5d22c : word).
Proof.
unfold fsm_run_u. intros fx mem0 rom sp ra a0v s tpv md off dtv ent key tsd ctx th tb te F V verb dto blk rec Hs_def Hret Hs Hok Htp Hmd Hoff Hdtv Hent Hkey Htsd Hctx Hth Htbe HF HV Hverb Hdto Hblk Hrec HC0 fs Hfs0 Hr HRfs h j pos ff top botth g40 g35 flag rs gcb Hfs Happm Hshz Hh Hj Hpos_def Hff_def Hng Hssl Hhint HF0 Hprobe Hflag Hwfs HG Hshadow_ok Htop Hth80 HCG HRS Hcol6 Hshok regs H10 H4 H2 H1.
assert (HFF : ff = (fs + 4096 + 32768 + 0 + 64 * pos)%Z) by (rewrite Hff_def; unfold gc_fr; pw (2 ^ (6 + 0))%Z; lia).
destruct (@fsm0_run_any fx mem0 rom sp ra a0v s tpv md off dtv ent key tsd ctx th tb te F V verb dto blk rec Hs_def Hret Hs Hok Htp Hmd Hoff Hdtv Hent Hkey Htsd Hctx Hth Htbe HF HV Hverb Hdto Hblk Hrec HC0 fs Hfs0 Hr HRfs h j pos ff top botth g40 g35 flag rs gcb Hfs Happm Hshz Hh Hj Hpos_def HFF Hng Hssl Hhint HF0 Hprobe Hflag Hwfs HG Hshadow_ok Htop Hth80 HCG HRS Hcol6 Hshok regs H10 H4 H2 H1) as (r' & Mf & RUN & Q10 & Q2 & Q1 & KCS & POST).
exists r', Mf. split; [exact RUN|]. split; [exact Q10|]. split; [exact Q2|]. split; [exact Q1|]. split; [exact KCS|]. exact POST.
Qed.
Lemma fsm_run_u_4 : fsm_run_u 4 (0x5d878 : word).
Proof.
unfold fsm_run_u. intros fx mem0 rom sp ra a0v s tpv md off dtv ent key tsd ctx th tb te F V verb dto blk rec Hs_def Hret Hs Hok Htp Hmd Hoff Hdtv Hent Hkey Htsd Hctx Hth Htbe HF HV Hverb Hdto Hblk Hrec HC0 fs Hfs0 Hr HRfs h j pos ff top botth g40 g35 flag rs gcb Hfs Happm Hshz Hh Hj Hpos_def Hff_def Hng Hssl Hhint HF0 Hprobe Hflag Hwfs HG Hshadow_ok Htop Hth80 HCG HRS Hcol6 Hshok regs H10 H4 H2 H1.
assert (HFF : ff = (fs + 4096 + 32768 + 4194304 + 1024 * pos)%Z) by (rewrite Hff_def; unfold gc_fr; pw (2 ^ (6 + 4))%Z; lia).
destruct (@fsm4_run_any fx mem0 rom sp ra a0v s tpv md off dtv ent key tsd ctx th tb te F V verb dto blk rec Hs_def Hret Hs Hok Htp Hmd Hoff Hdtv Hent Hkey Htsd Hctx Hth Htbe HF HV Hverb Hdto Hblk Hrec HC0 fs Hfs0 Hr HRfs h j pos ff top botth g40 g35 flag rs gcb Hfs Happm Hshz Hh Hj Hpos_def HFF Hng Hssl Hhint HF0 Hprobe Hflag Hwfs HG Hshadow_ok Htop Hth80 HCG HRS Hcol6 Hshok regs H10 H4 H2 H1) as (r' & Mf & RUN & Q10 & Q2 & Q1 & KCS & POST).
exists r', Mf. split; [exact RUN|]. split; [exact Q10|]. split; [exact Q2|]. split; [exact Q1|]. split; [exact KCS|]. exact POST.
Qed.
